module Lambda.PCFV.Term

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Subset

%default total

data Ty = A | Imp Ty Ty | C Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp

mutual
  data Val : List Ty -> Ty -> Type where
    Var  : Elem a g -> Val g a
    Zero : Val g A
    Succ : Val g A -> Val g A
    Lam  : Comp (a::g) b -> Val g (a~>b)
    Fix  : Comp (a::g) a -> Val g a
    Wrap : Comp g a -> Val g (C a)

  data Comp : List Ty -> Ty -> Type where
    V   : Val g a -> Comp g a
    App : Val g (a~>b) -> Val g a -> Comp g b
    If0 : Val g A -> Comp g a -> Comp (A::g) a -> Comp g a
    Bnd : Val g (C a) -> Comp (a::g) b -> Comp g b

mutual
  weakenV : Subset g d -> Val g a -> Val d a
  weakenV s (Var el) = Var $ s el
  weakenV s  Zero    = Zero
  weakenV s (Succ v) = Succ $ weakenV s v
  weakenV s (Lam c)  = Lam $ weakenC (ext s) c
  weakenV s (Fix c)  = Fix $ weakenC (ext s) c
  weakenV s (Wrap c) = Wrap $ weakenC s c

  weakenC : Subset g d -> Comp g a -> Comp d a
  weakenC s (V v)       = V $ weakenV s v
  weakenC s (App v u)   = App (weakenV s v) (weakenV s u)
  weakenC s (If0 v t f) = If0 (weakenV s v) (weakenC s t) (weakenC (ext s) f)
  weakenC s (Bnd v c)   = Bnd (weakenV s v) (weakenC (ext s) c)

lt : Comp g a -> Comp (a::g) b -> Comp g b
lt t u = Bnd (Wrap t) u

ap : Comp g (a~>b) -> Comp g a -> Comp g b
ap t u = lt t $ lt (weakenC There u) $ App (Var $ There Here) (Var Here)

bam : Comp g A
bam = App (Lam $ V Zero) (Fix $ V $ Succ $ Var Here)

fromN : Nat -> Val g A
fromN  Z    = Zero
fromN (S n) = Succ $ fromN n

plusN : Val g (A~>A~>A)
plusN = Fix $ V $ Lam $ V $ Lam $ If0 (Var $ There Here)
                                      (V $ Var Here)
                                      (lt (App (Var $ There $ There $ There Here) (Var Here)) $
                                       lt (App (Var Here) (Var $ There $ There Here)) $
                                          (V $ Succ $ Var Here))

plus32 : Comp g A
plus32 = ap (ap (V plusN) (V $ fromN 3)) (V $ fromN 2)

-- bigstep

mutual
  Env : List Ty -> Type
  Env = All Res

  data Res : Ty -> Type where
    RZ  : Res A
    RS  : Res A -> Res A
    RC  : Env g -> Comp g a -> Res (C a)
    RCl : Env g -> Comp (a::g) b -> Res (a~>b)

mutual
  evalV : Val g a -> Env g -> Res a
  evalV (Var el) env = indexAll el env
  evalV  Zero    env = RZ
  evalV (Succ v) env = RS $ evalV v env
  evalV (Lam t)  env = RCl env t
  evalV (Fix t)  env = assert_total $
                       evalC t (evalV (Fix t) env :: env)
  evalV (Wrap t) env = RC env t

  evalC : Comp g a -> Env g -> Res a
  evalC (V v)       env = evalV v env
  evalC (App t u)   env = case evalV t env of
    RCl env' c => assert_total $
                  evalC c (evalV u env :: env')
  evalC (If0 t u v) env = case evalV t env of
    RZ   => evalC u env
    RS r => evalC v (r :: env)
  evalC (Bnd v c)   env = case evalV v env of
                            RC e' c' => assert_total $
                                        evalC c (evalC c' e' :: env)
