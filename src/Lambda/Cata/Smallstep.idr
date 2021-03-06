module Lambda.Cata.Smallstep

import Data.Fin
import Data.Vect
import Data.List
import Data.List.Elem
import Subset
import Iter
import Lambda.Cata.Ty
import Lambda.Cata.Term

--%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var el)     = Var $ r el
rename r (Lam t)      = Lam $ rename (ext r) t
rename r (App t u)    = App (rename r t) (rename r u)
rename r (Pr t u)     = Pr (rename r t) (rename r u)
rename r (Fst t)      = Fst $ rename r t
rename r (Snd t)      = Snd $ rename r t
rename r (Inl t)      = Inl $ rename r t
rename r (Inr t)      = Inr $ rename r t
rename r (Case t u v) = Case (rename r t) (rename (ext r) u) (rename (ext r) v)
rename r  TT          = TT
rename r (In t)       = In $ rename r t
rename r (Ni t)       = Ni $ rename r t
rename r (Cata h t)   = Cata (rename r h) (rename r t)

Subst : List (Ty n) -> List (Ty n) -> Type
Subst {n} g d = {0 x : Ty n} -> Elem x g -> Term d x

exts : Subst g d -> Subst (b::g) (b::d)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst g d -> Term g a -> Term d a
subst s (Var el)     = s el
subst s (Lam t)      = Lam $ subst (exts s) t
subst s (App t u)    = App (subst s t) (subst s u)
subst s (Pr t u)     = Pr (subst s t) (subst s u)
subst s (Fst t)      = Fst $ subst s t
subst s (Snd t)      = Snd $ subst s t
subst s (Inl t)      = Inl $ subst s t
subst s (Inr t)      = Inr $ subst s t
subst s (Case t u v) = Case (subst s t) (subst (exts s) u) (subst (exts s) v)
subst s  TT          = TT
subst s (In t)       = In $ subst s t
subst s (Ni t)       = Ni $ subst s t
subst s (Cata h t)   = Cata (subst s h) (subst s t)

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
isVal (Pr t u)   = isVal t && isVal u
isVal (Inl t)    = isVal t
isVal (Inr t)    = isVal t
isVal (Cata _ _) = True
isVal  _         = False

data Imps : List (Ty n) -> Vect k (Ty 0) -> Vect k (Ty 0) -> Type where
  Nil  : Imps g [] []
  Cons : Term g (a~>b) -> Imps g as bs -> Imps g (a::as) (b::bs)

indexImps : {0 as, bs : Vect n (Ty 0)} -> Imps g as bs -> (k : Fin n) -> Term g (SubNT as k ~> SubNT bs k)
indexImps  Nil        k     = absurd k
indexImps (Cons t _)  FZ    = t
indexImps (Cons _ i) (FS k) = indexImps i k

rho : {r : Ty n} -> {as, bs : Vect n (Ty 0)} -> Imps g as bs -> Term g (substNT r as ~> substNT r bs)
rho {r=U}        tm = Lam $ Var Here
rho {r=TVar k}   tm = indexImps tm k
rho {r=Imp x y}  tm = Lam $ Lam $ App (rename (There . There) $ rho tm)
                                      (App (Var $ There Here) (Var Here))
rho {r=Prod x y} tm = Lam $ Pr (App (rename There $ rho tm) (Fst $ Var Here))
                               (App (rename There $ rho tm) (Snd $ Var Here))
rho {r=Sum x y}  tm = Lam $ Case (Var Here)
                                 (Inl $ App (rename (There . There) $ rho tm) (Var Here))
                                 (Inr $ App (rename (There . There) $ rho tm) (Var Here))
rho {r=Mu r}     tm = Lam $ Cata (Lam $ In $ App ((rename (There . There) $
                                                   rewrite subCons {a=substNT (Mu r) bs} {as} r in
                                                   rewrite subCons {a=substNT (Mu r) bs} {as=bs} r in
                                                   rho (Cons {a=substNT (Mu r) bs} (Lam $ Var Here) tm))) (Var Here))
                                 (Var Here)

step : {a : Ty n} -> Term g a -> Maybe (Term g a)
step (     Pr t u)       = [| Pr (step t) (pure u) |] <|> [| Pr (pure t) (step u) |]
step (Fst (Pr t u))      = Just t
step (Snd (Pr t u))      = Just u
step (      Fst t)       = Fst <$> step t
step (      Snd t)       = Snd <$> step t
step (      Inl t)       = Inl <$> step t
step (      Inr t)       = Inr <$> step t
step (Case (Inl t) u _)  = Just $ subst1 u t
step (Case (Inr t) _ v)  = Just $ subst1 v t
step (Case  t      u v)  = [| Case (step t) (pure u) (pure v) |]
step (In t)              = In <$> step t
step (Ni (In t))         = Just t
step (Ni t)              = Ni <$> step t
step (Cata {f} g (In t)) = Just $ App g (App (rewrite sub0_1N f (Mu f) in
                                              rewrite sub0_1N f a in
                                              rho (Cons (Lam $ Cata (rename There g) (Var Here)) Nil)) t)
step (Cata g t)          = [| Cata (pure g) (step t) |]
step (App (Lam t)  u)    = Just $ subst1 t u
step (App  t       u)    = if isVal t
                            then Nothing
                            else [| App (step t) (pure u) |]
step  _                  = Nothing

stepIter : {a : Ty n} -> Term g a -> Term g a
stepIter = iter step
