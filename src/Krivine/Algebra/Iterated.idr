module Krivine.Algebra.Iterated

import Krivine.Algebra.Terms
import Krivine.Algebra.Redex

%access public export
%default total

-- == Iterated head reduction ==

data Trace : Decomposition c -> Type where
  Done : {body : Tm (CC g s) t} -> {e : Env g} -> Trace (DecompVal body e)
  Step : Trace (decompose (plug (contract r) ctx)) -> Trace (Decompose r ctx)    

iterate : {c : Closed s} -> (d : Decomposition c) -> Trace d -> (c1 : Closed s ** Value c1)  
iterate (DecompVal body e)  Done     = (Clos (Lam body) e ** Val (Lam body) e)
iterate (Decompose r ctx)  (Step st) = iterate (decompose (plug (contract r) ctx)) st

Reducible : Closed s -> Type
Reducible {s=O}       c = Trace (decompose c)
Reducible {s=Arr s _} c = (Trace (decompose c), (x : Closed s) -> Reducible x -> Reducible (Clapp c x))

ReducibleEnv : Env g -> Type
ReducibleEnv  NE      = ()
ReducibleEnv (CE e c) = (Reducible c, ReducibleEnv e)

traceDecompose : Trace (decompose (headReduce c)) -> Trace (decompose c)
traceDecompose {c} t with (decompose c)
  traceDecompose t | DecompVal _ _ = t
  traceDecompose t | Decompose _ _ = Step t

snoc : EvalCon s (Arr t1 t2) -> Closed t1 -> EvalCon s t2 
snoc  MT          c = ARG c MT
snoc (ARG c1 ctx) c = ARG c1 (snoc ctx c)

data SnocView : EvalCon s t -> Type where
  RMT : SnocView MT
  RARG : (ctx : EvalCon s (Arr t t1)) -> (c : Closed t) -> SnocView (snoc ctx c)

snocView : (ctx : EvalCon s t) -> SnocView ctx
snocView MT = RMT
snocView (ARG c ctx) with (snocView ctx)
  snocView (ARG c MT)              | RMT          = RARG MT c
  snocView (ARG c (snoc ctx1 c1)) | RARG ctx1 c1 = RARG (ARG c ctx1) c1

plugSnoc : (c : Closed v) -> (ctx : EvalCon s (Arr v w)) -> (t : Closed s) -> plug t (snoc ctx c) = Clapp (plug t ctx) c
plugSnoc c MT           t = Refl
plugSnoc c (ARG c1 ctx) t = plugSnoc c ctx (Clapp t c1)

headReduceAppAux : (f : Closed (Arr s t)) -> (c : Closed s) -> {fc : Closed t} -> Clapp f c = fc -> Not (Value f) 
                -> headReduce fc = Clapp (headReduce f) c
headReduceAppAux f c {fc} eq nvf with (decompose fc)
  headReduceAppAux f c {fc=Clos (Lam body) e}      Refl nvf | DecompVal body e impossible
  headReduceAppAux f c {fc=plug (fromRedex r) ctx} eq   nvf | Decompose r ctx with (snocView ctx)
    headReduceAppAux f c Refl nvf | Decompose (Lookup _ _)  MT | RMT impossible
    headReduceAppAux f c Refl nvf | Decompose (Rapp _ _ _)  MT | RMT impossible
    headReduceAppAux f c eq   nvf | Decompose (Beta t e c1) MT | RMT with (clappU eq)
      headReduceAppAux f c eq   nvf | Decompose (Beta t e c1) MT | RMT | Refl = 
        absurd $ nvf $ rewrite fst $ clappInv eq in Val (Lam t) e
    headReduceAppAux f c eq   nvf | Decompose r (snoc ctx1 c1) | RARG ctx1 c1 with (clappU $ trans eq (plugSnoc c1 ctx1 (fromRedex r)))
      headReduceAppAux f c eq   nvf | Decompose r (snoc ctx1 c1) | RARG ctx1 c1 | Refl = 
        rewrite plugSnoc c1 ctx1 (contract r) in 
        let (eqf, eqc) = clappInv $ trans eq (plugSnoc c1 ctx1 (fromRedex r)) in
        rewrite eqf in
        rewrite eqc in
        rewrite headReducePlug r ctx1 in
        Refl

headReduceApp : (f : Closed (Arr s t)) -> (c : Closed s) -> Not (Value f)
                -> headReduce (Clapp f c) = Clapp (headReduce f) c
headReduceApp f c nvf = headReduceAppAux f c Refl nvf

headReduceAppApp : (c1 : Closed (Arr a (Arr b c))) -> (c2 : Closed a) -> (c3 : Closed b) 
                -> headReduce (Clapp (Clapp c1 c2) c3) = Clapp (headReduce (Clapp c1 c2)) c3
headReduceAppApp c1 c2 c3 = headReduceApp (Clapp c1 c2) c3 uninhabited

lemma1 : (c : Closed s) -> Reducible (headReduce c) -> Reducible c
lemma1 {s=O}       _                        h      = traceDecompose h
lemma1 {s=Arr _ _}   (Clos (Lam body) env) (tr, h) = (Done {body} {e=env}, h)
lemma1 {s=Arr _ _} c@(Clos (App _ _) _)    (tr, h) = (traceDecompose tr, \x, rx => lemma1 (Clapp c x) (h x rx))
lemma1 {s=Arr _ _} c@(Clos (Var _) _)      (tr, h) = (traceDecompose tr, \x, rx => lemma1 (Clapp c x) (h x rx))
lemma1 {s=Arr _ _} c@(Clapp f x)           (tr, h) = 
  (traceDecompose tr, 
   \x1, rx1 => lemma1 (Clapp c x1) $ rewrite headReduceAppApp f x x1 in h x1 rx1)

reducibleLookup : (e : Env g) -> (x : Ref g s) -> ReducibleEnv e -> Reducible (lookup e x)   
reducibleLookup  NE       Top    () impossible
reducibleLookup  NE      (Pop _) () impossible
reducibleLookup (CE _ _)  Top    (rc, _) = rc
reducibleLookup (CE e _) (Pop x) (_, re) = reducibleLookup e x re

lemma2 : (t : Tm g s) -> (e : Env g) -> ReducibleEnv e -> Reducible (Clos t e)   
lemma2 (Lam body) e re = (Done, \x, rx => lemma1 (Clapp (Clos (Lam body) e) x) (lemma2 body (CE e x) (rx, re)))
lemma2 (App f x)  e re = lemma1 (Clos (App f x) e) (snd (lemma2 f e re) (Clos x e) (lemma2 x e re))
lemma2 (Var i)    e re = lemma1 (Clos (Var i) e) (reducibleLookup e i re)

mutual    
  theorem : (c : Closed s) -> Reducible c
  theorem (Clos t e)  = lemma2 t e (envTheorem e)
  theorem (Clapp f x) = snd (theorem f) x (theorem x)

  envTheorem : (e : Env g) -> ReducibleEnv e
  envTheorem  NE      = ()
  envTheorem (CE e c) = (theorem c, envTheorem e)

termination : (c : Closed s) -> Trace (decompose c)
termination {s=O}       c = theorem c
termination {s=Arr _ _} c = fst (theorem c)

evaluate : Closed s -> (c1 : Closed s ** Value c1)
evaluate c = iterate (decompose c) (termination c)