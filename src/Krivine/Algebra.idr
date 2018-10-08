module Krivine.Algebra

%access public export
%default total

-- https://bitbucket.org/sergei.romanenko/agda-krivine-machine/

-- == Basic Terms ==

data Ty : Type where
  O : Ty
  Arr : Ty -> Ty -> Ty

-- De Bruijn contexts
data Con : Type where
  NC : Con
  CC : Con -> Ty -> Con
  
-- De Bruijn indices (the set of variables)
data Ref : Con -> Ty -> Type where
  Top : Ref (CC g s) s
  Pop : Ref g s -> Ref (CC g t) s

-- removing a variable from a context
rem : (g : Con) -> Ref g s -> Con
rem (CC g _)  Top    = g
rem (CC g s) (Pop x) = CC (rem g x) s

-- The set of terms
data Tm : Con -> Ty -> Type where
  Lam : Tm (CC g s) t -> Tm g (Arr s t)
  App : Tm g (Arr s t) -> Tm g s -> Tm g t
  Var : Ref g s -> Tm g s

-- Closed terms
mutual
  data Closed : Ty -> Type where
    Clos  : Tm g s -> Env g -> Closed s
    Clapp : Closed (Arr s t) -> Closed s -> Closed t

  data Env : Con -> Type where
    NE : Env NC
    CE : Env g -> Closed s -> Env (CC g s)

lookup : Env g -> Ref g s -> Closed s
lookup (CE _ c)  Top    = c
lookup (CE r _) (Pop x) = lookup r x

-- Values
data Value : Closed s -> Type where
  Val : (t : Tm g s) -> (e : Env g) -> Value (Clos t e)

Uninhabited (Value (Clapp _ _)) where
  uninhabited (Val _ _) impossible
  
valueDec : (c : Closed s) -> Dec (Value c)
valueDec (Clos t r)  = Yes (Val t r)
valueDec (Clapp _ _) = No absurd

-- == Redex and contraction ==
    
-- 1. decompose a closed term into a redex and an evaluation contex
-- 2. contract the redex to form a new closed term
-- 3. plug the resulting closed term back into the evaluation context

data Redex : Ty -> Type where
  Lookup : Ref g s -> Env g -> Redex s
  Rapp   : Tm g (Arr s t) -> Tm g s -> Env g -> Redex t
  Beta   : Tm (CC g s) t -> Env g -> Closed s -> Redex t

-- Reduction step

-- every redex can be mapped back to the closed term that it represents
fromRedex : Redex s -> Closed s
fromRedex (Lookup i env)   = Clos (Var i) env
fromRedex (Rapp f x env)   = Clos (App f x) env
fromRedex (Beta b env arg) = Clapp (Clos (Lam b) env) arg

-- the result of contracting a single redex
contract : Redex s -> Closed s
contract (Lookup i env)   = lookup env i
contract (Rapp f x env)   = Clapp (Clos f env) (Clos x env)
contract (Beta b env arg) = Clos b (CE env arg)

-- evaluation context as the list of arguments encountered along the spine of a term
data EvalCon : Ty -> Ty -> Type where
  MT  : EvalCon s s
  ARG : Closed s -> EvalCon t t1 -> EvalCon (Arr s t) t1

plug : Closed s -> EvalCon s t -> Closed t
plug f  MT         = f
plug f (ARG c ctx) = plug (Clapp f c) ctx  

data Decomposition : Closed s -> Type where
  DecompVal : (body : Tm (CC g s) t) -> (e : Env g) -> Decomposition (Clos (Lam body) e)
  Decompose : (r : Redex s) -> (ctx : EvalCon s t) -> Decomposition (plug (fromRedex r) ctx)

-- every closed term c can be decomposed into a Decomposition c

load : (c : Closed s) -> (ctx : EvalCon s t) -> Decomposition (plug c ctx)
load (Clos (Lam body) env)  MT           = DecompVal body env
load (Clos (Lam body) env) (ARG arg ctx) = Decompose (Beta body env arg) ctx
load (Clos (App f x) env)   ctx          = Decompose (Rapp f x env) ctx
load (Clos (Var i) env)     ctx          = Decompose (Lookup i env) ctx
load (Clapp c1 c2)          ctx          = load c1 (ARG c2 ctx)

decompose : (c : Closed s) -> Decomposition c
decompose c = load c MT

headReduce : Closed s -> Closed s
headReduce c with (decompose c)
  -- no further reduction to be done
  headReduce (Clos (Lam body) e)      | DecompVal body e = Clos (Lam body) e 
  -- contract the redex and plug the result back into the evaluation context
  headReduce (plug (fromRedex r) ctx) | Decompose r ctx  = plug (contract r) ctx 
