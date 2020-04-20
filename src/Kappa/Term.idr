module Kappa.Term

import Data.List

%default total
%access public export

data Ty = U | Prod Ty Ty

data Term : List (Ty, Ty) -> (Ty, Ty) -> Type where
  Var  : Elem xy g -> Term g xy
  Id   : Term g (x,x)
  Bang : Term g (t,Prod t U)
  Comp : Term g (x,y) -> Term g (y,z) -> Term g (x,z)
  Lift : Term g (U,x) -> Term g (y,Prod x y)
  Kap  : Term ((U,x)::g) (y,z) -> Term g (Prod x y,z)

ap : Term g (Prod x y,z) -> Term g (U,x) -> Term g (y,z)
ap t u = Comp (Lift u) t

assoc : Term g (Prod x (Prod y z), Prod (Prod x y) z)
assoc = Kap $ Kap $ Lift $ Comp (Var Here) (Lift $ Var $ There Here)

isoL : Term g (Prod U x, y) -> Term g (x, y)
isoL t = ap t Id

isoR : Term g (Prod x U, y) -> Term g (x, y)
isoR = Comp Bang

prodL1 : Term g (t,Prod U t)
prodL1 = Lift Id

dropL : Term g (Prod s t,t)
dropL = Kap Id

dropR1 : Term g (Prod t U, t)
dropR1 = Kap $ Var Here

discard : Term g (t,U)
discard = isoR dropL

copy : Term g (t,Prod t t)
copy = isoR $ Kap $ Comp (Var Here) (Lift $ Var Here)

swap : Term g (Prod s t, Prod t s)
swap = Kap $ isoR $ Kap $ Comp (Var $ There Here) (Lift $ Var Here)
