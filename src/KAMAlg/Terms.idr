module KAMAlg.Terms

%access public export
%default total

-- == Basic Terms ==

-- STLC types
data Ty : Type where
  O   : Ty
  Arr : Ty -> Ty -> Ty

-- De Bruijn contexts (a snoc-list of types)
data Con : Type where
  NC : Con
  CC : Con -> Ty -> Con
  
-- De Bruijn indices (the set of variables)
data Ref : Con -> Ty -> Type where
  Top : Ref (CC g s) s
  Pop : Ref g s -> Ref (CC g t) s

-- removing a variable from a context (not really needed)
rem : (g : Con) -> Ref g s -> Con
rem (CC g _)  Top    = g
rem (CC g s) (Pop x) = CC (rem g x) s

-- STLC terms
data Tm : Con -> Ty -> Type where
  Lam : Tm (CC g s) t -> Tm g (Arr s t)
  App : Tm g (Arr s t) -> Tm g s -> Tm g t
  Var : Ref g s -> Tm g s

-- Closed terms
-- a variation of Curien’s λρ-calculus, proposed in 
-- Biernacka, Danvy, "A concrete framework for environment machines"
mutual
  data Closed : Ty -> Type where
    -- A closure is a term t paired with an environment containing closed terms 
    -- for all the free variables in t
    Clos  : Tm g s -> Env g -> Closed s
    -- closed terms are closed under application
    Clapp : Closed (Arr s t) -> Closed s -> Closed t

  data Env : Con -> Type where
    NE : Env NC
    CE : Env g -> Closed s -> Env (CC g s)

clappInv : Clapp f x = Clapp g y -> (f = g, x = y)
clappInv Refl = (Refl, Refl)

clappU : {f : Closed (Arr u v)} -> {g : Closed (Arr w v)} -> Clapp f x = Clapp g y -> u = w
clappU Refl = Refl

-- look up the variable from the environment 
lookup : Env g -> Ref g s -> Closed s
lookup (CE _ c)  Top    = c
lookup (CE r _) (Pop x) = lookup r x

-- Closed lambda expressions are the only values
data Value : Closed s -> Type where
  Val : (t : Tm g s) -> (e : Env g) -> Value (Clos t e)

Uninhabited (Value (Clapp _ _)) where
  uninhabited (Val _ _) impossible
  
valueDec : (c : Closed s) -> Dec (Value c)
valueDec (Clos t r)  = Yes (Val t r)
valueDec (Clapp _ _) = No absurd