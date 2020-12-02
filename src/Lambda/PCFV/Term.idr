module Lambda.PCFV.Term

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Subset
import Iter

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
    Wrap : Comp g a -> Val g (C a)

  data Comp : List Ty -> Ty -> Type where
    V   : Val g a -> Comp g a
    App : Val g (a~>b) -> Val g a -> Comp g b
    If0 : Val g A -> Comp g a -> Comp (A::g) a -> Comp g a
    Fix : Comp (a::g) a -> Comp g a
    Bnd : Val g (C a) -> Comp (a::g) b -> Comp g b

mutual
  renameV : Subset g d -> Val g a -> Val d a
  renameV s (Var el) = Var $ s el
  renameV s  Zero    = Zero
  renameV s (Succ v) = Succ $ renameV s v
  renameV s (Lam c)  = Lam $ renameC (ext s) c
  renameV s (Wrap c) = Wrap $ renameC s c

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

plus32 : Comp g A
plus32 = ap (ap plusN (V $ fromN 3)) (V $ fromN 2)

-- bigstep

mutual
  Env : List Ty -> Type
  Env = All Res

  data Res : Ty -> Type where
    RZ  : Res A
    RS  : Res A -> Res A
    RC  : Res a -> Res (C a)
    RCl : Env g -> Comp (a::g) b -> Res (a~>b)

mutual
  evalV : Val g a -> Env g -> Res a
  evalV (Var el) env = indexAll el env
  evalV  Zero    _   = RZ
  evalV (Succ v) env = RS $ evalV v env
  evalV (Lam t)  env = RCl env t
  evalV (Wrap t) env = RC $ evalC t env

  evalC : Comp g a -> Env g -> Res a
  evalC (V v)       env = evalV v env
  evalC (App t u)   env = case evalV t env of
    RCl env' c => assert_total $
                  evalC c (evalV u env :: env')
  evalC (If0 t u v) env = case evalV t env of
    RZ   => evalC u env
    RS r => evalC v (r :: env)
  evalC (Fix t)     env = assert_total $
                          evalC t (evalC (Fix t) env :: env)
  evalC (Bnd v c)   env = case evalV v env of
                            RC r => evalC c (r :: env)

-- smallstep

SubstV : List Ty -> List Ty -> Type
SubstV g d = {0 x : Ty} -> Elem x g -> Val d x

extsV : SubstV g d -> SubstV (b::g) (b::d)
extsV _  Here      = Var Here
extsV s (There el) = renameV There (s el)

mutual
  substVV : SubstV g d -> Val g a -> Val d a
  substVV s (Var el) = s el
  substVV s  Zero    = Zero
  substVV s (Succ v) = Succ $ substVV s v
  substVV s (Lam c)  = Lam $ substVC (extsV s) c
  substVV s (Wrap c) = Wrap $ substVC s c

  substVC : SubstV g d -> Comp g a -> Comp d a
  substVC s (V v)       = V $ substVV s v
  substVC s (App v w)   = App (substVV s v) (substVV s w)
  substVC s (If0 v c d) = If0 (substVV s v) (substVC s c) (substVC (extsV s) d)
  substVC s (Fix c)     = Fix $ substVC (extsV s) c
  substVC s (Bnd v c)   = Bnd (substVV s v) (substVC (extsV s) c)

sub1 : Val g a -> SubstV (a::g) g
sub1 v  Here      = v
sub1 v (There el) = Var el

subst1VV : Val g a -> Val (a::g) b -> Val g b
subst1VV v w = substVV (sub1 v) w

subst1VC : Val g a -> Comp (a::g) b -> Comp g b
subst1VC v c = substVC (sub1 v) c

subst1CC : Comp g a -> Comp (a::g) b -> Comp g b
subst1CC (V v)       e = subst1VC v e
subst1CC (App {a=aa} {b=bb} v w)   e = ?wat
subst1CC (If0 v c d) e = ?wat2
subst1CC (Fix c)     e = ?wat3
subst1CC (Bnd v c)   e = Bnd v (subst1CC c (renameC (permute . There) e))

stepV : Comp g a -> Maybe (Comp g a)
stepV (App (Lam c) v)    = Just $ subst1VC v c
--stepV (Succ m)           = Succ <$> stepV m
stepV (If0  Zero    t f) = Just t
stepV (If0 (Succ v) t f) = Just $ subst1VC v f
--stepV (If0 p t f)        = (\q => If0 q t f) <$> stepV p
--stepV (Fix f)            = Just $ ?wat
stepV (Bnd (Wrap c) d)   = Just $ subst1CC c d
stepV  _                 = Nothing

stepIterV : Comp g a -> (Nat, Comp g a)
stepIterV = iterCount stepV
