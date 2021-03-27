module Lambda.Untyped.Strong.KN4

-- from Munk, [2008] "A Study of Syntactic and Semantic Artifacts and its Application to Lambda Definability, Strong Normalization, and Weak Normalization in the Presence of State"

import Iter
import Lambda.Untyped.Term

%default total

mutual
  data Clos = Cl Term Env
            | Lv Nat

  Env : Type
  Env = List Clos

mutual
  data MStack = Mt
              | TM Term Stack  -- ANF
              | L MStack

  data Stack = M MStack | C Term Env Nat Stack

data State = More1 Term Env Stack Nat
           | More2 Stack Term -- ANF
           | More3 Stack Term Env Nat
           | More4 MStack Term
           | Done Term

init : Term -> State
init t = More1 t [] (M Mt) Z

step : State -> Maybe State
step (More1 (App t u)            e  s m) = Just $ More1 t            e (C u e m s)     m
step (More1 (Lam t)              e  s m) = Just $ More3 s t e m
step (More1 (Var (S n))      (_::e) s m) = Just $ More1 (Var n)      e          s      m
step (More1 (Var  Z)      (Lv n::_) s m) = Just $ More2 s (Var $ minus m n)
step (More1 (Var  Z)    (Cl t e::_) s m) = Just $ More1 t            e          s      m
step (More1 (Var  n)            []  s m) = Just $ More2 s (Var $ n+m)

step (More2 (M ms)      a)               = Just $ More4 ms a
step (More2 (C t e m s) a)               = Just $ More1 t            e (M (TM a s))    m

step (More3 (M ms)        t e m)         = Just $ More1 t (Lv (S m)::e)  (M (L ms)) (S m)
step (More3 (C t1 e1 _ s) t e m)         = Just $ More1 t (Cl t1 e1::e)         s      m

step (More4 Mt       t )                 = Just $ Done t
step (More4 (L s)    t )                 = Just $ More4 s (Lam t)
step (More4 (TM a s) t )                 = Just $ More2 s (App a t)

step  _                                  = Nothing

run : Term -> (Nat, State)
run t = iterCount step (init t)
