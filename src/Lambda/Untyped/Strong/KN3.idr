module Lambda.Untyped.Strong.KN3

-- from Garcia-Perez, Nogueira, [2019] "The full-reducing Krivine abstract machine KN simulates pure normal-order reduction in lockstep: A proof via corresponding calculus"

import Iter
import Lambda.Untyped.Term

%default total
--%access public export

mutual
  data Clos = Cl Term Env
            | Lv Nat
            | Rs Term

  Env : Type
  Env = List Clos

data Frame = L | TM Term | C Term Env

Stack : Type
Stack = List Frame

data State = More Clos Stack Nat
           | Done Term

init : Term -> State
init t = More (Cl t []) [] Z

step : State -> Maybe State
step (More (Cl (App t u)        e)           s     m ) = Just $ More (Cl t            e )        (C u e::s)    m
step (More (Cl (Lam t)          e) (C t1 e1::s)    m ) = Just $ More (Cl t (Cl t1 e1::e))                s     m
step (More (Cl (Lam t)          e)           s     m ) = Just $ More (Cl t (Lv (S m)::e))            (L::s) (S m)
step (More (Cl (Var  Z)    (c::_))           s     m ) = Just $ More  c                                  s     m
step (More (Cl (Var (S n)) (_::e))           s     m ) = Just $ More (Cl (Var n)      e )                s     m
step (More (Cl (Var  n)        [])           s     m ) = Just $ More (Rs $ Var (n+m))                    s     m
step (More (Lv  n)                           s     m ) = Just $ More (Rs $ Var $ minus m n)              s     m
step (More (Rs t)                           []     m ) = Just $ Done t
step (More (Rs t)                   (C t1 e::s)    m ) = Just $ More (Cl t1 e)                    (TM t::s)    m
step (More (Rs t)                        (L::s) (S m)) = Just $ More (Rs (Lam t))                        s     m
step (More (Rs u)                     (TM t::s)    m ) = Just $ More (Rs (App t u))                      s     m
step  _                                              = Nothing

run : Term -> (Nat, State)
run t = iterCount step (init t)
