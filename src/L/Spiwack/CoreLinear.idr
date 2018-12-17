module L.CoreLinear

%access public export
%default total

data Ty = AL | AR

dual : Ty -> Ty
dual AL = AR
dual AR = AL

dualInv : dual (dual a) = a
dualInv {a=AL} = Refl
dualInv {a=AR} = Refl

mutual 
  data Cmd : List Ty -> Type where 
    C : Term g a -> Term g (dual a) -> Cmd (g ++ d)

  data Term : List Ty -> Ty -> Type where
    Var   : Term [a] a
    Covar : Term [a] (dual a)
    Mu    : Cmd (a::g) -> Term g (dual a)