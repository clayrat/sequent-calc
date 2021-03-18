module Lambda.Untyped.Strong.KN2

-- from Biernacka, Biernacki, Charatonik, Drab, [2020] "An Abstract Machine for Strong Call by Value"

import Iter
import Lambda.Untyped.Term

%default total

data TermN = T Term | V Nat

mutual
  Env : Type
  Env = List Clos

  data Clos = Cl TermN Env

data Stor = L | TM Term | C Clos

Stack : Type
Stack = List Stor

data State = More1 TermN Env Stack Nat
           | More2 Stack Term Nat
           | Done Term

init : Term -> State
init t = More1 (T t) [] [] Z

step : State -> Maybe State
step (More1 (T (App t1 t2))           e        s  m) = Just $ More1 (T t1)                        e  (C (Cl (T t2) e)::s)    m
step (More1 (T (Lam t))               e  (C c::s) m) = Just $ More1 (T t)                     (c::e)                   s     m
step (More1 (T (Lam t))               e        s  m) = Just $ More1 (T t)       (Cl (V (S m)) []::e)               (L::s) (S m)
step (More1 (T (Var  Z))     (Cl t e::_)       s  m) = Just $ More1    t                          e                    s     m
step (More1 (T (Var (S n)))       (_::e)       s  m) = Just $ More1 (T $ Var n)                   e                    s     m
step (More1 (V  n)                    _        s  m) = Just $ More2 s (Var $ minus m n)  m
step (More2               []                   t  Z) = Just $ Done t
step (More2 (C (Cl t1 e1)::s)                  t  m) = Just $ More1    t1                         e1            (TM t::s)    m
step (More2            (L::s)                  t  m) = Just $ More2 s (Lam t)           (minus m 1)
step (More2        (TM t1::s)                  t  m) = Just $ More2 s (App t1 t)         m
step  _                                                        = Nothing

run : Term -> (Nat, State)
run t = iterCount step (init t)
