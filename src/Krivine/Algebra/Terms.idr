module Krivine.Algebra.Terms

%access public export
%default total

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

clappInv : Clapp f x = Clapp g y -> (f = g, x = y)
clappInv Refl = (Refl, Refl)

clappU : {f : Closed (Arr u v)} -> {g : Closed (Arr w v)} -> Clapp f x = Clapp g y -> u = w
clappU Refl = Refl

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