module Lambda.Cata.Smallstep

import Data.Fin
import Data.List
import Subset
import Iter
import Lambda.Cata.Ty
import Lambda.Cata.Term

%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Pair t u)   = Pair (rename r t) (rename r u)
rename r (Fst t)      = Fst $ rename r t
rename r (Snd t)      = Snd $ rename r t
rename r (Inl t)      = Inl $ rename r t
rename r (Inr t)      = Inr $ rename r t
rename r (Case t u v) = Case (rename r t) (rename (ext r) u) (rename (ext r) v)
rename r  TT          = TT
rename r (In t)       = In $ rename r t
rename r (Cata t)     = Cata $ rename r t

Subst : List (Ty n) -> List (Ty n) -> Type
Subst {n} g d = {x : Ty n} -> Elem x g -> Term d x

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
subst s (Inl t)      = Inl $ subst s t
subst s (Inr t)      = Inr $ subst s t
subst s (Case t u v) = Case (subst s t) (subst (exts s) u) (subst (exts s) v)
subst s  TT          = TT
subst s (In t)       = In $ subst s t
subst s (Cata t)     = Cata $ subst s t

subst1 : Term (a::g) b -> Term g a -> Term g b
subst1 {g} {a} t s = subst {g=a::g} go t
  where
  go : Subst (a::g) g
  go  Here      = s
  go (There el) = Var el

isVal : Term g a -> Bool
isVal (Lam _)    = True
isVal (Var _)    = True
isVal  TT        = True
isVal (Pair t u) = isVal t && isVal u
isVal (Inl t)    = isVal t
isVal (Inr t)    = isVal t
isVal  _         = False

rho : Term g (a ~> b) -> Term g (subst1T f a ~> subst1T f b)
rho {f=U}           tm = Lam $ Var Here
rho {f=TVar FZ}     tm = tm
rho {f=TVar (FS n)} tm = Lam $ Var Here
rho {f=Imp x y}     tm = Lam $ Lam $ App (rename (There . There) $ rho {f=y} tm) (App (Var $ There Here) (Var Here))
rho {f=Prod x y}    tm = Lam $ Pair (App (rename There $ rho {f=x} tm) (Fst $ Var Here))
                                    (App (rename There $ rho {f=y} tm) (Snd $ Var Here))
rho {f=Sum x y}     tm = Lam $ Case (Var Here)
                                    (Inl $ App (rename (There . There) $ rho {f=x} tm) (Var Here))
                                    (Inr $ App (rename (There . There) $ rho {f=y} tm) (Var Here))
rho {f=Mu f} {a}{b} tm = ?wat
                         --Cata $ Lam $ In $ App (rename There $ rho {a=Mu b} ?wat) (Var Here)

step : Term g a -> Maybe (Term g a)
step (     Pair t u)       = [| Pair (step t) (step u) |]
step (Fst (Pair t u))      = Just t
step (Snd (Pair t u))      = Just u
step (      Inl t)         = Inl <$> step t
step (      Inr t)         = Inr <$> step t
step (Case (Inl t) u _)    = Just $ subst1 u t
step (Case (Inr t) _ v)    = Just $ subst1 v t
step (In t)                = In <$> step t
step (Cata t)              = Cata <$> step t
step (App (Lam t)  u)      = Just $ subst1 t u
step (App (Cata f) (In t)) = Just $ App f (App (rho (Cata f)) t)
step (App  t       u)      =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step  _                    = Nothing

stepIter : Term g a -> Term g a
stepIter = iter step
