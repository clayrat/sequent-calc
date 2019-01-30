module Lambda.STLC.CPS

import Data.List
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- from https://github.com/YouyouCong/type-preserving-cps/blob/master/stlc.agda

-- CPS language

data TyC = AC | ImpT TyC TyC | ImpC TyC TyC
  
data TermC : List TyC -> List TyC -> TyC -> Type where
  VarT : Elem a g -> TermC g g1 a
  VarC : Elem a g1 -> TermC g g1 a
  LamT : TermC (a::g) g1 b -> TermC g g1 (ImpT a b)
  LamC : TermC g (a::g1) b -> TermC g g1 (ImpC a b)
  AppT : TermC g g1 (ImpT a b) -> TermC g g1 a -> TermC g g1 b
  AppC : TermC g g1 (ImpC a b) -> TermC g g1 a -> TermC g g1 b

-- CPS translation

-- translation for types
mutual
  trans : Ty -> TyC
  trans a = ImpC (ImpC (transAux a) AC) AC

  transAux : Ty -> TyC
  transAux  A        = AC
  transAux (Imp a b) = ImpT (trans a) (trans b)  

mapElem : (f : a -> b) -> Elem x xs -> Elem (f x) (f <$> xs)
mapElem f  Here      = Here
mapElem f (There el) = There $ mapElem f el

-- Within Γ n ensures n <= length Γ
data Within : List a -> Nat -> Type where
  OkZ : Within g Z
  OkS : Within g n -> Within (x::g) (S n)

-- add T to Γ as the nth element
addToNth : (g : List a) -> (n : Nat) -> Within g n -> a -> List a
addToNth  g         Z     OkZ    t = t :: g
addToNth (x :: xs) (S k) (OkS y) t = x :: addToNth xs k y t

-- shift the variable x if the index is greater than or equal to n
varShiftAboveN : Elem a g -> (n : Nat) -> {p : Within g n} -> Elem a (addToNth g n p b)
varShiftAboveN  el         Z    {p=OkZ}   = There el
varShiftAboveN  Here      (S _) {p=OkS _} = Here
varShiftAboveN (There el) (S k) {p=OkS p} = There $ varShiftAboveN el k {p}

termShiftAboveN : TermC g g1 a -> (n : Nat) -> {p : Within g1 n} -> TermC g (addToNth g1 n p b) a
termShiftAboveN (VarT el)    _     = VarT el
termShiftAboveN (VarC el)    n     = VarC $ varShiftAboveN el    n
termShiftAboveN (LamT t)     n     = LamT $ termShiftAboveN t    n 
termShiftAboveN (LamC t)     n {p} = LamC $ termShiftAboveN t (S n) {p=OkS p}
termShiftAboveN (AppT t1 t2) n     = AppT (termShiftAboveN t1 n) (termShiftAboveN t2 n)
termShiftAboveN (AppC t1 t2) n     = AppC (termShiftAboveN t1 n) (termShiftAboveN t2 n)

-- weakening
wkc : TermC g g1 b -> TermC g (a::g1) b
wkc (VarT el)    = VarT el
wkc (VarC el)    = VarC $ There el
wkc (LamT t)     = LamT $ wkc t
wkc (LamC t)     = LamC $ termShiftAboveN t 1 {p=OkS OkZ}
wkc (AppT t1 t2) = AppT (wkc t1) (wkc t2)
wkc (AppC t1 t2) = AppC (wkc t1) (wkc t2)

-- CPS translation
cps : Term g a -> TermC (map trans g) [] (trans a)
cps (Var el)    = VarT $ mapElem trans el
cps (Lam t)     = LamC $ AppC (VarC Here) (wkc $ LamT $ cps t)
cps (App t1 t2) = LamC $ AppC (wkc $ cps t1) (LamC $ AppC (AppT (VarC Here) (wkc $ wkc $ cps t2)) (VarC $ There Here))
