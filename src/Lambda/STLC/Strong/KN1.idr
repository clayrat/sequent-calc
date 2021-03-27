module Lambda.STLC.Strong.KN1

import Data.Stream

import Data.List
import Data.List.Elem
import Data.List.Quantifiers
--import Data.List.Views
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total

mutual
  data Env : List Ty -> Type where
    Nil : Env []
    (::) : Clos a -> Env g -> Env (a::g)
    Lv : Nat -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : List Ty -> Ty -> Ty -> Type where
  Mt : Stack [] a a
  C  : Clos a -> Stack d b c -> Stack d (a~>b) c
  L  : Stack d (a~>b) c -> Stack (a::d) b c
  TM : Term d (a~>b) -> Stack d b c -> Stack d a c

data State : Ty -> Type where
  More1 : Term g a -> Env g -> Stack d a b -> Nat -> State b
  More2 : Stack d a b -> Term d a -> Nat -> State b
  Done  : Term [] a -> State a

-- [ 1 2 3 ]
--   [ 2 3 ]
-- some kind of thinning?

step : State c -> Maybe (State c)
step (More1 (App t1 t2)               e       s  m) = Just $ More1 t1                 e  (C (Cl t2 e) s)    m
step (More1 (Lam t)                   e  (C c s) m) = Just $ More1 t              (c::e)              s     m
step (More1 (Lam t)                   e       s  m) = Just $ More1 t        (Lv (S m) e)           (L s) (S m)
step (More1 (Var (There el))      (_::e)      s  m) = Just $ More1 (Var el)           e               s     m
step (More1 (Var (There el))    (Lv _ e)      s  m) = Just $ More1 (Var el)           e               s     m
step (More1 (Var Here)       (Cl t e::_)      s  m) = Just $ More1 t                  e               s     m
-- m-n = Elem a d
step (More1 (Var Here)          (Lv n e)      s  m) = Just $ More2 s (Var ?sub) m
step (More2             Mt t    Z )                 = Just $ Done t
step (More2 (C (Cl t e) s) u    m )                 = Just $ More1 t                  e         (TM u s)    m
step (More2          (L s) t (S m))                 = Just $ More2 s (Lam t)    m
step (More2       (TM t s) u    m )                 = Just $ More2 s (App t u)  m
step  _                                             = Nothing

init : Term [] a -> State a
init t = More1 t [] Mt Z
