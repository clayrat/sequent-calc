module ABDM.VCLS

import Lambda.Untyped.Term

%default total
%access public export

data I = Access Nat 
       | Lmb (List I)
       | Push
       | Ap 

compile : Term -> List I
compile (Var n)   = [Access n]
compile (Lam t)   = [Lmb (compile t)]
compile (App t u) = Push :: compile t ++ compile u ++ [Ap]

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl (List I) Env

Stack : Type
Stack = List Clos  

State : Type
State = (List I, List Env, Stack)

step : State -> Maybe State
step (Access  Z   ::c, (v::_)::l,             s) = Just (          c,         l,       v::s)
step (Access (S n)::c, (v::e)::l,             s) = Just (Access n::c,      e::l,          s)
step (      Lmb c1::c,      e::l,             s) = Just (          c,         l, Cl c1 e::s)
step (          Ap::c,         l, v::Cl c1 e::s) = Just (      c1++c, (v::e)::l,          s)
step (        Push::c,      e::l,             s) = Just (          c,   e::e::l,          s)
step _                                           = Nothing