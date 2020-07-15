module ES.SuspCalc.LamSig1

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
    Id     : Subs g g
    Shift  : (n : Nat) -> Subs (drop (S n) g) d -> Subs g d
    Cons   : Tm g a -> Subs g d -> Subs g (a::d)

id : Subs g g
id = Id

cons : Tm g a -> Subs g d -> Subs g (a::d)
cons = Cons

lift : Subs g d -> Subs (a::g) (a::d)
lift s = Cons (Var Here) (Shift Z s)

lookup1 : {d : List Ty} -> (o : Nat) -> Elem a g -> Subs (drop o d) g -> Tm d a
lookup1  o     el         Id         = Var $ addToElem o el
lookup1  o     el        (Shift n s) = assert_total $
                                       lookup1 (S n + o) el (rewrite sym $ dropSum (S n) o d in s)
lookup1  Z     Here      (Cons t s)  = t
lookup1 (S o)  Here      (Cons t s)  = Clos t (Shift o Id)
lookup1  o    (There el) (Cons t s)  = lookup1 o el s

lookup : {d : List Ty} -> Elem a g -> Subs d g -> Tm d a
lookup el s = lookup1 Z el s

compose : Subs g e -> Subs e d -> Subs g d
compose  Id          u              = u
-- coverage checker bug? can't replace `Cons t s` with just `s`
compose (Cons t s)   Id             = Cons t s
compose (Shift n s)  u              = Shift n (compose s u)
compose (Cons t s)  (Shift  Z    u) = compose s u
compose (Cons t s)  (Shift (S n) u) = compose s (Shift n u)
compose  s          (Cons t u)      = Cons (Clos t s) (compose s u)

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
step  _                   = Nothing

stepIter : {g : List Ty} -> Tm g a -> Tm g a
stepIter = iter step
