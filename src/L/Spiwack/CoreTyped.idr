module L.CoreTyped

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
    C : Term g a -> Term g (dual a) -> Cmd g

  data Term : List Ty -> Ty -> Type where
    Var   : Term (a::g) a
    Covar : Term (a::g) (dual a)
    Mu    : Cmd (a::g) -> Term g (dual a)

weaken : Cmd [AL, AL] -> Cmd [AL]
weaken c = C (Mu c) Var

muvcv : Term [] AR
muvcv = Mu $ C {a=AL} Var Covar

-- `C mucvc mucvc` cannot be typed
