module ABDM.VKAM

import Iter
import Lambda.Untyped.Term

%default total
%access public export

data I = Access Nat
       | Push (List I)    -- one step of unrolling
       | Grab             -- one step of beta-reduction

compile : Term -> List I
compile (Var n)   = [Access n]
compile (Lam t)   = Grab :: compile t
compile (App t u) = Push (compile u) :: compile t

mutual
  Env : Type
  Env = List Clos

  data Clos = Cl (List I) Env

Stack : Type
Stack = List Clos    -- spine of term being reduced (the term whose code is in the code pointer)

State : Type
State = (List I, Env, Stack)

step : State -> Maybe State
step (Access  Z   ::_, Cl c e::_,     s) = Just (          c,     e,          s)
step (Access (S n)::c,      _::e,     s) = Just (Access n::c,     e,          s)
step (Grab        ::c,         e, c0::s) = Just (          c, c0::e,          s)
step (Push c1     ::c,         e,     s) = Just (          c,     e, Cl c1 e::s)
step  _                                  = Nothing

run : Term -> (Nat, State)
run t = iterCount step (compile t, [], [])