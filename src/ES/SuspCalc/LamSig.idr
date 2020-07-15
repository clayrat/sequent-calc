module ES.SuspCalc.LamSig

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
    Id    : Subs g g
    Shift : Subs (a::g) g
    Cons  : Tm g a -> Subs g d -> Subs g (a::d)
    Comp  : Subs g e -> Subs e d -> Subs g d

id : Subs g g
id = Id

cons : Tm g a -> Subs g d -> Subs g (a::d)
cons = Cons

lift : Subs g d -> Subs (a::g) (a::d)
lift s = Cons (Var Here) (Comp Shift s)

compose : Subs g e -> Subs e d -> Subs g d
compose = Comp

lookup : Elem a g -> Subs d g -> Tm d a
lookup  e         Id                     = Var e
lookup  e         Shift                  = Var $ There e
lookup  Here     (Cons t _)              = t
lookup (There e) (Cons _ s)              = lookup e s
lookup  e        (Comp s Id)             = lookup e s
lookup  e        (Comp s Shift)          = lookup (There e) s
-- totality checker bug?
lookup  e        (Comp s (Cons t r))  =
  case e of
    Here => Clos t s
    There e => assert_total $ lookup e (Comp s r)
--lookup  Here     (Comp s (Cons t _))     = Clos t s
--lookup (There e) (Comp s (Cons _ r))     = lookup e (Comp s r)
lookup  e        (Comp s (Comp r q))     = assert_total $ lookup e (Comp (Comp s r) q)

encode : Term g a -> Tm g a
encode (Var el)  = Var el
encode (Lam t)   = Lam $ encode t
encode (App t u) = App (encode t) (encode u)

isVal : Tm g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

step : Tm g a -> Maybe (Tm g a)
step (App (Lam t)     u ) = Just $ Clos t (cons u id)
step (App  t          u ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Clos (Var e)    s ) = Just $ lookup e s
step (Clos  t         Id) = Just t
step (Clos (App t u)  s ) = Just $ App (Clos t s) (Clos u s)
step (Clos (Lam t)    s ) = Just $ Lam $ Clos t (lift s)
step (Clos (Clos t s) r ) = Just $ Clos t (compose r s)
step  _                                        = Nothing
step  _                                        = Nothing

stepIter : Tm g a -> Tm g a
stepIter = iter step
