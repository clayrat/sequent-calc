module Lambda.PCFV.Term

import Data.List
import Data.List.Elem
import Subset

%default total

public export
data Ty = A | Imp Ty Ty | C Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

mutual
  public export
  data Val : List Ty -> Ty -> Type where
    Var  : Elem a g -> Val g a
    Zero : Val g A
    Succ : Val g A -> Val g A
    Lam  : Comp (a::g) b -> Val g (a~>b)
    Wrap : Comp g a -> Val g (C a)

  public export
  data Comp : List Ty -> Ty -> Type where
    V   : Val g a -> Comp g a
    App : Val g (a~>b) -> Val g a -> Comp g b
    If0 : Val g A -> Comp g a -> Comp (A::g) a -> Comp g a
    Fix : Comp (a::g) a -> Comp g a
    Bnd : Val g (C a) -> Comp (a::g) b -> Comp g b

mutual
  export
  renameV : Subset g d -> Val g a -> Val d a
  renameV s (Var el) = Var $ s el
  renameV s  Zero    = Zero
  renameV s (Succ v) = Succ $ renameV s v
  renameV s (Lam c)  = Lam $ renameC (ext s) c
  renameV s (Wrap c) = Wrap $ renameC s c

  export
  renameC : Subset g d -> Comp g a -> Comp d a
  renameC s (V v)       = V $ renameV s v
  renameC s (App v u)   = App (renameV s v) (renameV s u)
  renameC s (If0 v t f) = If0 (renameV s v) (renameC s t) (renameC (ext s) f)
  renameC s (Fix c)     = Fix $ renameC (ext s) c
  renameC s (Bnd v c)   = Bnd (renameV s v) (renameC (ext s) c)

lt : Comp g a -> Comp (a::g) b -> Comp g b
lt t u = Bnd (Wrap t) u

ap : Comp g (a~>b) -> Comp g a -> Comp g b
ap t u = lt t $ lt (renameC There u) $ App (Var $ There Here) (Var Here)

export
bam : Comp g A
bam = ap (V $ Lam $ V Zero) (Fix $ V $ Succ $ Var Here)

fromN : Nat -> Val g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

plusN : Comp g (A~>A~>A)
plusN = Fix $ V $ Lam $ V $ Lam $ If0 (Var $ There Here)
                                      (V $ Var Here)
                                      (lt (App (Var $ There $ There $ There Here) (Var Here)) $
                                       lt (App (Var Here) (Var $ There $ There Here)) $
                                          (V $ Succ $ Var Here))

export
plus32 : Comp g A
plus32 = ap (ap plusN (V $ fromN 3)) (V $ fromN 2)
