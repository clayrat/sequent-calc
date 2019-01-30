module Lambda.Untyped.CLS

import Lambda.Untyped.Term

%default total
%access public export

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

data Dir : Type where
  T : Term -> Dir
  Ap : Dir

State : Type
State = (List Dir, List Env, Stack)

step : State -> Maybe State
step (T (Var  Z   )::c, (v::_)::l,            s) = Just (              c,         l,      v::s)
step (T (Var (S n))::c, (v::e)::l,            s) = Just (   T (Var n)::c,      e::l,         s)
step (T (Lam t    )::c,      e::l,            s) = Just (              c,         l, Cl t e::s)
step (T (App t u  )::c,      e::l,            s) = Just (T t::T u::Ap::c,   e::e::l,         s)
step (           Ap::c,         l, v::Cl t e::s) = Just (         T t::c, (v::e)::l,         s)
step _                                              = Nothing