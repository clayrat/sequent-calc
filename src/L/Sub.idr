module L.Sub

import Data.List.Elem
import Subset

%default total

data Ty = A
        | Imp Ty Ty | Prod Ty Ty
        | Sub Ty Ty | Sum  Ty Ty

mutual
  data Cmd : List Ty -> List Ty -> Type where
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    Lam  : Term (a::g) b d -> Term g (Imp a b) d
    CApp : Term g a d -> CoTerm g b d -> Term g (Sub a b) d
    Pair : Term g a d -> Term g b d -> Term g (Prod a b) d
    Inl  : Term g a d -> Term g (Sum a b) d
    Inr  : Term g b d -> Term g (Sum a b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d
    AppC  : Term g a d -> CoTerm g b d -> CoTerm g (Imp a b) d
    SLam  : CoTerm g a (b::d) -> CoTerm g (Sub a b) d
    MatP  : Cmd (a::b::g) d -> CoTerm g (Prod a b) d
    MatS  : Cmd (a::g) d -> Cmd (b::g) d -> CoTerm g (Sum a b) d

mutual
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1
  shiftTerm (Var el)   = Var $ shift is1 el
  shiftTerm (Mu c)     = Mu $ shiftCmd c
  shiftTerm (Lam t)    = Lam $ shiftTerm t
  shiftTerm (CApp t e) = CApp (shiftTerm t) (shiftCoTerm e)
  shiftTerm (Pair t u) = Pair (shiftTerm t) (shiftTerm u)
  shiftTerm (Inl t1)   = Inl $ shiftTerm t1
  shiftTerm (Inr t2)   = Inr $ shiftTerm t2

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1
  shiftCoTerm (CoVar el)   = CoVar $ shift is2 el
  shiftCoTerm (Mut c)      = Mut $ shiftCmd c
  shiftCoTerm (AppC t e)   = AppC (shiftTerm t) (shiftCoTerm e)
  shiftCoTerm (SLam e)     = SLam $ shiftCoTerm e
  shiftCoTerm (MatP c)     = MatP $ shiftCmd c
  shiftCoTerm (MatS c1 c2) = MatS (shiftCmd c1) (shiftCmd c2)

fst : Term g (Prod a b) d -> Term g a d
fst t = Mu $ C (shiftTerm t) (MatP $ C (Var Here) (CoVar Here))

snd : Term g (Prod a b) d -> Term g b d
snd t = Mu $ C (shiftTerm t) (MatP $ C (Var $ There Here) (CoVar Here))

curry : Term g (Imp (Prod a b) c) d -> Term g (Imp a (Imp b c)) d
curry t = Lam $ Lam $ Mu $ C (shiftTerm t) (AppC (Pair (Var $ There Here) (Var Here)) (CoVar Here))

uncurry : Term g (Imp a (Imp b c)) d -> Term g (Imp (Prod a b) c) d
uncurry t = Lam $ Mu $ C (shiftTerm t) (AppC (fst $ Var Here) (AppC (snd $ Var Here) (CoVar Here)))

outl : CoTerm g (Sum a b) d -> CoTerm g a d
outl e = Mut $ C (Inl $ Var Here) (shiftCoTerm e)

outr : CoTerm g (Sum a b) d -> CoTerm g b d
outr e = Mut $ C (Inr $ Var Here) (shiftCoTerm e)

subHd : Term g (Sub a b) d -> Term g a d
subHd t = Mu $ C (shiftTerm t) (SLam $ CoVar $ There Here)

cocurry : Term g (Imp a (Sum b c)) d -> Term g (Imp (Sub a b) c) d
cocurry t = Lam $ Mu $ C (shiftTerm t)
                         (AppC (subHd $ Var Here)
                               (MatS (C (Var $ There Here)
                                        (SLam $ Mut $ C (Var $ There Here) (CoVar Here)))
                                     (C (Var Here) (CoVar Here))))

councurry : Term g (Imp (Sub a b) c) d -> Term g (Imp a (Sum b c)) d
councurry t = Lam $ Mu $ C (shiftTerm t)
                           (AppC (CApp (Var Here) (outl $ CoVar Here)) (outr $ CoVar Here))
