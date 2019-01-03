module Lambda.Lam

import Data.List
import Lambda.Ty

%default total
%access public export

-- untyped

data Tm0 = Vr0 Nat | Lm0 Tm0 | Ap0 Tm0 Tm0

Term0 : Tm0
Term0 = Ap0 (Lm0 $ Ap0 (Vr0 Z) (Vr0 Z)) (Lm0 $ Vr0 Z)

Term1 : Tm0
Term1 = Ap0 (Ap0 (Lm0 $ Vr0 Z) (Lm0 $ Vr0 Z)) (Lm0 $ Vr0 Z)

Term2 : Tm0
Term2 = Ap0 (Lm0 $ Vr0 Z) (Ap0 (Lm0 $ Vr0 Z) (Lm0 $ Vr0 Z))

-- STLC

data Tm : List Ty -> Ty -> Type where
  Vr : Elem a g -> Tm g a 
  Lm : Tm (a::g) b -> Tm g (a~>b)
  Ap : Tm g (a~>b) -> Tm g a -> Tm g b
  
TestTy : Ty
TestTy = A~>A

TestTm1 : Tm [] TestTy
TestTm1 = Ap (Ap (Lm $ Vr Here) (Lm $ Vr Here)) (Lm $ Vr Here)

TestTm2 : Tm [] TestTy
TestTm2 = Ap (Lm $ Vr Here) (Ap (Lm $ Vr Here) (Lm $ Vr Here))

ResultTm : Tm [] TestTy
ResultTm = Lm $ Vr Here  