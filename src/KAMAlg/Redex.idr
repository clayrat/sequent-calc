module KAMAlg.Redex

import KAMAlg.Terms

%access public export
%default total

-- == Redex and contraction ==

-- a small step evaluator in that normalizes by repeated head reduction 

-- LOOKUP : i[c_1, c_2,...c_n] -> c_i 
-- APP    : (t_0 t_1)[env] -> (t_0[env]) (t_1[env]) 
-- BETA   : ((λt)[env]) x -> t[x · env] 
-- LEFT   : if c_0 -> c'_0 then c_0 c_1 -> c'_0 c_1

-- define a single reduction step in three parts:
-- (in the style of Danvy, Nielsen, "Refocusing in Reduction Semantics")

-- 1. decompose a closed term into a redex and an evaluation contex
-- 2. contract the redex to form a new closed term
-- 3. plug the resulting closed term back into the evaluation context

data Redex : Ty -> Type where
  Lookup : Ref g s -> Env g -> Redex s
  Rapp   : Tm g (Arr s t) -> Tm g s -> Env g -> Redex t
  Beta   : Tm (CC g s) t -> Env g -> Closed s -> Redex t

-- every redex can be mapped back to the closed term that it represents
fromRedex : Redex s -> Closed s
fromRedex (Lookup i env)   = Clos (Var i) env
fromRedex (Rapp f x env)   = Clos (App f x) env
fromRedex (Beta b env arg) = Clapp (Clos (Lam b) env) arg

-- the result of contracting a single redex
contract : Redex s -> Closed s
contract (Lookup i env)   = lookup env i
-- distributes the environment over the two terms
contract (Rapp f x env)   = Clapp (Clos f env) (Clos x env)
-- extends the environment with the argument arg, and uses the extended environment 
-- to create a new closure from the body of a lambda
contract (Beta b env arg) = Clos b (CE env arg)

-- evaluation context is the list of arguments (closed terms) encountered 
-- along the spine of a term
data EvalCon : (src : Ty) -> (dst : Ty) -> Type where
  MT  : EvalCon s s
  ARG : Closed s -> EvalCon t t1 -> EvalCon (Arr s t) t1

-- applies any arguments from the evaluation context to its argument term  
plug : Closed s -> EvalCon s t -> Closed t
plug f  MT         = f
plug f (ARG c ctx) = plug (Clapp f c) ctx  

-- decomposition of a closed term into a redex and evaluation context as a view on closed terms
data Decomposition : (c : Closed s) -> Type where
  -- c is a value, in which case we have the closure of a Lam-term and an environment
  DecompVal : (body : Tm (CC g s) t) -> (e : Env g) -> Decomposition (Clos (Lam body) e)
  -- plugging the term corresponding to r in the evaluation context ctx is equal to c
  Decompose : (r : Redex s) -> (ctx : EvalCon s t) -> Decomposition (plug (fromRedex r) ctx)

-- traverses the spine of c, accumulating any arguments we encounter in an evaluation context
-- until we find a redex or a closure containing a Lam
load : (c : Closed s) -> (ctx : EvalCon s t) -> Decomposition (plug c ctx)
load (Clos (Lam body) env)  MT           = DecompVal body env
load (Clos (Lam body) env) (ARG arg ctx) = Decompose (Beta body env arg) ctx
load (Clos (App f x) env)   ctx          = Decompose (Rapp f x env) ctx
load (Clos (Var i) env)     ctx          = Decompose (Lookup i env) ctx
load (Clapp c1 c2)          ctx          = load c1 (ARG c2 ctx)

-- inspects the evaluation context that load has accumulated in order to decide if a lambda is 
-- indeed a value, or whether it still has further arguments, and hence corresponds to a Beta redex
unload : (ctx : EvalCon (Arr s t) r) -> (body : Tm (CC g s) t) -> (e : Env g) -> Decomposition (plug (Clos (Lam body) e) ctx) 
unload  MT            body env = DecompVal body env 
unload (ARG arg ctx ) body env = Decompose (Beta body env arg) ctx 

-- every closed term c can be decomposed into a Decomposition c
decompose : (c : Closed s) -> Decomposition c
decompose c = load c MT

headReduce : Closed s -> Closed s
headReduce c with (decompose c)
  -- no further reduction to be done
  headReduce (Clos (Lam body) e)      | DecompVal body e = Clos (Lam body) e 
  -- contract the redex and plug the result back into the evaluation context
  headReduce (plug (fromRedex r) ctx) | Decompose r ctx  = plug (contract r) ctx 

decomposePlug : (c : Closed s) -> (ctx : EvalCon s t) -> decompose (plug c ctx) = load c ctx
decomposePlug _  MT          = Refl
decomposePlug c (ARG c1 ctx) = decomposePlug (Clapp c c1) ctx

loadFromRedex : (r : Redex s) -> (ctx : EvalCon s t) -> load (fromRedex r) ctx = Decompose r ctx
loadFromRedex (Lookup _ _) _ = Refl
loadFromRedex (Rapp _ _ _) _ = Refl
loadFromRedex (Beta _ _ _) _ = Refl

headReducePlug : (r : Redex s) -> (ctx : EvalCon s t) -> headReduce (plug (fromRedex r) ctx) = plug (contract r) ctx
headReducePlug r ctx = 
  rewrite decomposePlug (fromRedex r) ctx in 
  rewrite loadFromRedex r ctx in  
  Refl

-- an auxiliary "backwards view" on evaluation contexts that states that every evaluation 
-- context is either empty or arises by adding a closed term to the end of an evaluation context
snoc : EvalCon s (Arr t1 t2) -> Closed t1 -> EvalCon s t2 
snoc  MT          c = ARG c MT
snoc (ARG c1 ctx) c = ARG c1 (snoc ctx c)

data SnocView : EvalCon s t -> Type where
  RMT  : SnocView MT
  RARG : (ctx : EvalCon s (Arr t t1)) -> (c : Closed t) -> SnocView (snoc ctx c)

snocView : (ctx : EvalCon s t) -> SnocView ctx
snocView  MT = RMT
snocView (ARG c ctx) with (snocView ctx)
  snocView (ARG c  MT)            | RMT          = RARG MT c
  snocView (ARG c (snoc ctx1 c1)) | RARG ctx1 c1 = RARG (ARG c ctx1) c1

plugSnoc : (c : Closed v) -> (ctx : EvalCon s (Arr v w)) -> (t : Closed s) -> plug t (snoc ctx c) = Clapp (plug t ctx) c
plugSnoc c  MT          t = Refl
plugSnoc c (ARG c1 ctx) t = plugSnoc c ctx (Clapp t c1)

headReduceAppAux : (f : Closed (Arr s t)) -> (c : Closed s) -> {fc : Closed t} -> Clapp f c = fc -> Not (Value f) 
                -> headReduce fc = Clapp (headReduce f) c
headReduceAppAux f c {fc} eq nvf with (decompose fc)
  headReduceAppAux f c {fc=Clos (Lam body) e     } Refl nvf | DecompVal body e impossible
  headReduceAppAux f c {fc=plug (fromRedex r) ctx} eq   nvf | Decompose r ctx with (snocView ctx)
    headReduceAppAux f c Refl nvf | Decompose (Lookup _ _)  MT | RMT impossible
    headReduceAppAux f c Refl nvf | Decompose (Rapp _ _ _)  MT | RMT impossible
    headReduceAppAux f c eq   nvf | Decompose (Beta t e c1) MT | RMT with (clappU eq)
      headReduceAppAux f c eq   nvf | Decompose (Beta t e c1) MT | RMT | Refl = 
        absurd $ nvf $ rewrite fst $ clappInv eq in 
                       Val (Lam t) e
    headReduceAppAux f c eq   nvf | Decompose r (snoc ctx1 c1) | RARG ctx1 c1 with (clappU $ trans eq $ plugSnoc c1 ctx1 (fromRedex r))
      headReduceAppAux f c eq   nvf | Decompose r (snoc ctx1 c1) | RARG ctx1 c1 | Refl = 
        rewrite plugSnoc c1 ctx1 (contract r) in 
        let (eqf, eqc) = clappInv $ trans eq $ plugSnoc c1 ctx1 (fromRedex r) in
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