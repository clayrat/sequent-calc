module Lambda.STLC.Strong.KN4

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total

mutual
  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a
    Lv : Nat -> Clos a

  Env : List Ty -> Type
  Env = All Clos

mutual
  data MStack : List Ty -> Ty -> Ty -> Type where
    Mt : MStack [] a a
    TM : Term d (a~>b) -> Stack d b c -> MStack d a c -- ANF
    L  : MStack d (a~>b) c -> MStack (a::d) b c

  data Stack : List Ty -> Ty -> Ty -> Type where
    M : MStack d a b -> Stack d a b
    C : Term g a -> Env g -> Nat -> Stack d b c -> Stack d (a~>b) c

data State : Ty -> Type where
  More1 : Term g a -> Env g -> Stack d a b -> Nat -> State b
  More2 : Stack d a b -> Term d a -> State b  -- ANF
  More3 : Stack d (a~>b) c -> Term (a::g) b -> Env g -> Nat -> State c
  More4 : MStack d a b -> Term d a -> State b -- NF
  Done  : Term [] a -> State a

step : State z -> Maybe (State z)
step (More1 (App t u)                 e  s m) = Just $ More1 t            e (C u e m s)     m
step (More1 (Lam t)                   e  s m) = Just $ More3 s t e m
step (More1 (Var (There el))      (_::e) s m) = Just $ More1 (Var el)     e          s      m
step (More1 (Var  Here)        (Lv n::_) s m) = Just $ More2 s (Var ?wat) --minus m n
step (More1 (Var  Here)      (Cl t e::_) s m) = Just $ More1 t            e          s      m
--step (More1 (Var  el)            []  s m) = Just $ More2 s (Var $ n+m) -- not gonna work like this: Elem el []

step (More2 (M ms)      a)                    = Just $ More4 ms a
step (More2 (C t e m s) a)                    = Just $ More1 t            e (M (TM a s))    m

step (More3 (M ms)        t e m)              = Just $ More1 t (Lv (S m)::e)  (M (L ms)) (S m)
step (More3 (C t1 e1 _ s) t e m)              = Just $ More1 t (Cl t1 e1::e)         s      m

step (More4 Mt       t )                      = Just $ Done t
step (More4 (L s)    t )                      = Just $ More4 s (Lam t)
step (More4 (TM a s) t )                      = Just $ More2 s (App a t)

step  _                                       = Nothing

init : Term [] a -> State a
init t = More1 t [] (M Mt) Z
