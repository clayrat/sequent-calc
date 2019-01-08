module KAM.Alg.Iterated

import KAM.Alg.Terms
import KAM.Alg.Redex

%access public export
%default total

-- == Iterated head reduction ==

-- using the Bove-Capretta method: structural recursion over the call graph of a function   
data Trace : Decomposition c -> Type where
  Done : {body : Tm (CC g s) t} -> {e : Env g} -> Trace (DecompVal body e)
  Step : Trace (decompose (plug (contract r) ctx)) -> Trace (Decompose r ctx)
  
-- the traces themselves carry no computational content  
collapsible : (d : Decomposition c) -> (t1, t2 : Trace d) -> t1 = t2 
collapsible (DecompVal _ _)     Done      Done     = Refl
collapsible (Decompose r ctx)  (Step t1) (Step t2) = cong $ collapsible (decompose (plug (contract r) ctx)) t1 t2

iterate : {c : Closed s} -> (d : Decomposition c) -> Trace d -> (c1 : Closed s ** Value c1)  
iterate (DecompVal body e)  Done     = (Clos (Lam body) e ** Val (Lam body) e)
iterate (Decompose r ctx)  (Step st) = iterate (decompose (plug (contract r) ctx)) st

-- logical relation that strengthens our induction hypothesis
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

lemma1 : (c : Closed s) -> Reducible (headReduce c) -> Reducible c
lemma1 {s=O}       _                        h      = traceDecompose h
lemma1 {s=Arr _ _}   (Clos (Lam body) env) ( _, h) = (Done {body} {e=env}, h)
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

  -- every closed term in the environment is also reducible
  envTheorem : (e : Env g) -> ReducibleEnv e
  envTheorem  NE      = ()
  envTheorem (CE e c) = (theorem c, envTheorem e)

termination : (c : Closed s) -> Trace (decompose c)
termination {s=O}       c = theorem c
termination {s=Arr _ _} c = fst (theorem c)

-- iteratively perform a single step of head reduction
evaluate : Closed s -> (c1 : Closed s ** Value c1)
evaluate c = iterate (decompose c) (termination c)