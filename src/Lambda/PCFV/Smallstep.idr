module Lambda.PCFV.Smallstep

import Data.List.Elem
import Subset
import Iter
import Lambda.PCFV.Term

%default total

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
