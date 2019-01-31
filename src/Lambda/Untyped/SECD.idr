module Lambda.Untyped.SECD

import Iter
import Lambda.Untyped.Term

%default total
%access public export

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

data Dir = T Term | Ap

Snapshot : Type 
Snapshot = (Stack, Env, List Dir)

Dump : Type
Dump = List Snapshot

State : Type
State = (Snapshot, Dump)

step : State -> Maybe State 
step ((            s, e,   T (Var i)::c),               d) = (\x=>((     x::s ,    e ,               c ),          d)) <$> index' i e 
step ((            s, e,   T (Lam t)::c),               d) = Just ((Cl t e::s ,    e ,               c ),          d)
step ((            s, e, T (App t u)::c),               d) = Just ((        s ,    e , T u::T t::Ap::c ),          d)
step ((Cl t e1::v::s, e,          Ap::c),               d) = Just ((       [] , v::e1,           [T t] ), (s,e,c)::d) 
step ((         v::_, _,             []), (s1, e1, c1)::d) = Just ((     v::s1,    e1,               c1),          d)
step _ = Nothing

runSECD : Term -> (Nat, Maybe State)
runSECD t = iterCount step (([], [], [T t]), [])
