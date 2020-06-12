module ES.LamZet.Typed

import Data.List.Elem
import Iter
import Elem
import Lambda.STLC.Ty
import Lambda.STLC.Term

--%access public export
%default total

mutual
  public export
  data Tm : List Ty -> Ty -> Type where
    Var  : Elem a g -> Tm g a
    Lam  : Tm (a::g) b -> Tm g (a~>b)
    App  : Tm g (a~>b) -> Tm g a -> Tm g b
    MApp : Tm g (a~>b) -> Tm g a -> Tm g b
    RApp : Tm g (a~>b) -> Tm g a -> Tm g b
    Clos : Tm g a -> Subs d g -> Tm d a

  public export
  data Subs : List Ty -> List Ty -> Type where
    Lift  : Subs g d -> Subs (a::g) (a::d)
    Slash : Tm g a -> Subs g (a::g)
    Shift : Subs (a::g) g

encode : Term g a -> Tm g a
encode (Var el)  = Var el
encode (Lam t)   = Lam $ encode t
encode (App t u) = App (encode t) (encode u)

isVal : Tm g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Tm g a -> Maybe (Tm g a)
step (App (Lam t)            u       ) = Just $ Clos t (Slash u)
step (MApp (Lam t)           u       ) = Just $ Clos t (Slash u)
step (App  t                 u       ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Clos (Lam t)           s       ) = Just $ Lam (Clos t (Lift s))
step (Clos (Var Here)       (Slash t)) = Just t
step (Clos (Var (There el)) (Slash t)) = Just $ Var el
step (Clos (Var Here)       (Lift s) ) = Just $ Var Here
step (Clos (Var (There el)) (Lift s) ) = Just $ Clos (Clos (Var el) s) Shift
step (Clos (Var el)          Shift   ) = Just $ Var $ There el
step (Clos (RApp t u)        s       ) = Just $ App (Clos t s) (Clos u s)
step (Clos (App t u)         s       ) = Just $ Clos (MApp t u) s
step (MApp (Var el)          u       ) = Just $ RApp (Var el) u
step (MApp (App t u)         v       ) = Just $ MApp (MApp t u) v
step (MApp (RApp t u)        v       ) = Just $ RApp (RApp t u) v
step  _                                = Nothing

stepIter : Tm g a -> Tm g a
stepIter = iter step
