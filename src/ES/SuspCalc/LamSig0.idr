module ES.SuspCalc.LamSig0

import Data.Nat
import Data.List
import Data.List.Elem
import Iter
import Elem
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total

mutual
  public export
  data Tm : List Ty -> Ty -> Type where
    Var  : Elem a g -> Tm g a
    Lam  : Tm (a::g) b -> Tm g (a~>b)
    App  : Tm g (a~>b) -> Tm g a -> Tm g b
    Clos : Tm g a -> Subs d g -> Tm d a

  public export
  data Subs : List Ty -> List Ty -> Type where
    Shift  : (n : Nat) -> Subs g (drop n g)
    Cons   : Tm g a -> Subs g d -> Subs g (a::d)

id : Subs g g
id = Shift 0

cons : Tm g a -> Subs g d -> Subs g (a::d)
cons = Cons

compose : Subs g e -> Subs e d -> Subs g d
compose (Shift n)  (Shift  m   ) = rewrite dropSum m n g in Shift (m+n)
compose  r         (Shift  Z   ) = r
compose (Cons _ u) (Shift (S n)) = compose u (Shift n)
compose  r         (Cons t s)    = Cons (Clos t r) (compose r s)

lift : Subs g d -> Subs (a::g) (a::d)
lift s = Cons (Var Here) (compose (Shift 1) s)

lookup : {d : List Ty} -> Elem a g -> Subs d g -> Tm d a
lookup  Here     (Cons t _) = t
lookup (There e) (Cons _ s) = lookup e s
lookup  e        (Shift n)  = Var $ addToElem n e

encode : Term g a -> Tm g a
encode (Var el)  = Var el
encode (Lam t)   = Lam $ encode t
encode (App t u) = App (encode t) (encode u)

isVal : Tm g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : {g : List Ty} -> Tm g a -> Maybe (Tm g a)
step (App (Lam t)     u ) = Just $ Clos t (cons u id)
step (App  t          u ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Clos (Var e)    s ) = Just $ lookup e s
step (Clos (App t u)  s ) = Just $ App (Clos t s) (Clos u s)
step (Clos (Lam t)    s ) = Just $ Lam $ Clos t (lift s)
step (Clos (Clos t s) r ) = Just $ Clos t (compose r s)
step  _                                        = Nothing

stepIter : {g : List Ty} -> Tm g a -> Tm g a
stepIter = iter step
