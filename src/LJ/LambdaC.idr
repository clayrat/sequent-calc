module LJ.LambdaC

import Data.List
import Iter
import Subset
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- Moggi's lambda-C

mutual
  data Val : List Ty -> Ty -> Type where
    Var : Elem a g -> Val g a
    Lam : Tm (a::g) b -> Val g (a~>b)

  data Tm : List Ty -> Ty -> Type where
    V   : Val g a -> Tm g a
    App : Tm g (a~>b) -> Tm g a -> Tm g b
    Let : Tm g a -> Tm (a::g) b -> Tm g b

mutual
  renameVal : Subset g d -> Val g a -> Val d a
  renameVal sub (Var el) = Var $ sub el
  renameVal sub (Lam t)  = Lam $ renameTm (ext sub) t

  renameTm : Subset g d -> Tm g a -> Tm d a
  renameTm sub (V v)     = V $ renameVal sub v
  renameTm sub (App t u) = App (renameTm sub t) (renameTm sub u)
  renameTm sub (Let m n) = Let (renameTm sub m) (renameTm (ext sub) n)

shiftVal : {auto is : IsSubset g d} -> Val g a -> Val d a
shiftVal {is} = renameVal (shift is)

shiftTm : {auto is : IsSubset g d} -> Tm g a -> Tm d a
shiftTm {is} = renameTm (shift is)

-- substitution on terms

Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x d -> Tm g x

Sid : Subst g g
Sid = V . Var

Slmap : Subset g1 g2 -> Subst g1 d -> Subst g2 d
Slmap f s = renameTm f . s

SCons : Tm g a -> Subst g d -> Subst g (a::d)
SCons t s  Here      = t
SCons t s (There el) = s el

weak : Subst g d -> Subst (a::g) d
weak = Slmap There

exts : Subst g d -> Subst (b::g) (b::d)
exts s = SCons (V $ Var Here) (weak s)

mutual
  substVal : Subst g d -> Val d a -> Tm g a
  substVal s (Var el)    = s el
  substVal s (Lam t)     = V $ Lam $ substTm (exts s) t

  substTm : Subst g d -> Tm d a -> Tm g a
  substTm s (V v)     = substVal s v
  substTm s (App t u) = App (substTm s t) (substTm s u)
  substTm s (Let m n) = Let (substTm s m) (substTm (exts s) n)

subst1 : Tm (a::g) b -> Tm g a -> Tm g b
subst1 t s = substTm (SCons s Sid) t

-- substitution on values

SubstV : List Ty -> List Ty -> Type
SubstV g d = {x : Ty} -> Elem x d -> Val g x

SidV : SubstV g g
SidV = Var

SlmapV : Subset g1 g2 -> SubstV g1 d -> SubstV g2 d
SlmapV f s = renameVal f . s

SConsV : Val g a -> SubstV g d -> SubstV g (a::d)
SConsV t s  Here      = t
SConsV t s (There el) = s el

weakV : SubstV g d -> SubstV (a::g) d
weakV = SlmapV There

extsV : SubstV g d -> SubstV (b::g) (b::d)
extsV s = SConsV (Var Here) (weakV s)

mutual
  substValV : SubstV g d -> Val d a -> Val g a
  substValV s (Var el)    = s el
  substValV s (Lam t)     = Lam $ substTmV (extsV s) t

  substTmV : SubstV g d -> Tm d a -> Tm g a
  substTmV s (V v)     = V $ substValV s v
  substTmV s (App t u) = App (substTmV s t) (substTmV s u)
  substTmV s (Let m n) = Let (substTmV s m) (substTmV (extsV s) n)

subst1V : Val (a::g) b -> Val g a -> Val g b
subst1V t s = substValV (SConsV s SidV) t

-- reduction

isVal : Tm g a -> Bool
isVal (V _) = True
isVal _ = False

step : Tm g a -> Maybe (Tm g a)
step (App   (V (Lam m)) v@(V _)         ) = Just $ subst1 m v
step (App v@(V _)       n               ) = Just $ Let n (App (renameTm There v) (V $ Var Here))
step (App m             n               ) = Just $ Let m (App (V $ Var Here) (renameTm There n))
step (Let v@(V _)       m               ) = Just $ subst1 m v
step (Let m               (V (Var Here))) = Just m
step (Let (Let m n)     p               ) = Just $ Let m (Let n (renameTm (ext There) p))
step (Let m             n               ) = [| Let (step m) (pure n) |]
step  _                                   = Nothing

stepIter : Tm [] a -> (Nat, Tm [] a)
stepIter = iterCount step

-- STLC conversion

embedLC : Term g a -> Tm g a
embedLC (Var e)     = V $ Var e
embedLC (Lam t)     = V $ Lam $ embedLC t
embedLC (App t1 t2) = App (embedLC t1) (embedLC t2)

mutual
  forgetVal : Val g a -> Term g a
  forgetVal (Var el) = Var el
  forgetVal (Lam t)  = Lam $ forgetTm t

  forgetTm : Tm g a -> Term g a
  forgetTm (V v)     = forgetVal v
  forgetTm (App m n) = App (forgetTm m) (forgetTm n)
  forgetTm (Let n m) = App (Lam $ forgetTm m) (forgetTm n)
