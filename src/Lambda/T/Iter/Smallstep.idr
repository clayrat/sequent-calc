module Lambda.T.Iter.Smallstep

import Data.List
import Subset
import Iter
import Lambda.T.Iter.Ty
import Lambda.T.Iter.Term

%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Pair t u)   = Pair (rename r t) (rename r u)
rename r (Fst t)      = Fst $ rename r t
rename r (Snd t)      = Snd $ rename r t
rename r  Zero        = Zero
rename r (Succ n)     = Succ $ rename r n
rename r (Iter t u v) = Iter (rename r t) (rename r u) (rename r v)

recN : Term g N -> Term g a -> Term g (a ~> N ~> a) -> Term g a
recN t u v = Fst $ Iter t (Pair u Zero) (Lam $ Pair (App (App (rename There v) (Fst $ Var Here)) (Snd $ Var Here)) (Succ $ Snd $ Var Here))

Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x g -> Term d x

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst g d -> Term g a -> Term d a
subst s (Var el)     = s el
subst s (Lam t)      = Lam $ subst (exts s) t
subst s (App t u)    = App (subst s t) (subst s u)
subst s (Pair t u)   = Pair (subst s t) (subst s u)
subst s (Fst t)      = Fst $ subst s t
subst s (Snd t)      = Snd $ subst s t
subst s  Zero        = Zero
subst s (Succ n)     = Succ $ subst s n
subst s (Iter t u v) = Iter (subst s t) (subst s u) (subst s v)

subst1 : Term (a::g) b -> Term g a -> Term g b
subst1 {g} {a} t s = subst {g=a::g} go t
  where
  go : Subst (a::g) g
  go  Here      = s
  go (There el) = Var el

isVal : Term g a -> Bool
isVal (Lam _)  = True
isVal (Var _)  = True
isVal  Zero    = True
isVal (Succ n) = isVal n
isVal  _       = False

step : Term g a -> Maybe (Term g a)
step (Succ t           ) = Succ <$> step t
step (Iter  Zero    u _) = Just u
step (Iter (Succ t) u v) = Just $ App v (Iter t u v)
step (App (Lam t)  u   ) = Just $ subst1 t u
step (App  t       u   ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step  _ = Nothing

stepIter : Term g a -> Term g a
stepIter = iter step