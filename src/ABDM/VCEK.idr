module ABDM.VCEK

import Iter
import Lambda.Untyped.Term

%default total
%access public export

data I = Access Nat
       | Push (List I)
       | Close (List I)

compile : Term -> List I
compile (Var n)   = [Access n]
compile (Lam t)   = [Close (compile t)]
compile (App t u) = Push (compile u) :: compile t

mutual
  Env : Type
  Env = List Clos

  data Clos = Cl (List I) Env

data Stack : Type where
  Mt : Stack
  C1 : List I -> Env -> Stack -> Stack
  C2 : Clos -> Stack -> Stack

State : Type
State = Either (Stack, Clos) (List I, Env, Stack)

step : State -> Maybe State
step (Right (Access  Z   ::_, c::_, k)) = Just $ Left (k, c)
step (Right (Access (S n)::c, _::e, k)) = Just $ Right (Access n::c, e, k)
step (Right (Close c1    ::c,    e, k)) = Just $ Left (k, Cl c1 e)
step (Right (Push c1     ::c,    e, k)) = Just $ Right (c, e, C1 c1 e k)
step (Left (C1     c e  k, v)) = Just $ Right (c,    e, C2 v k)
step (Left (C2 (Cl c e) k, v)) = Just $ Right (c, v::e,      k)
step  _ = Nothing

run : Term -> (Nat, State)
run t = iterCount step (Right (compile t, [], Mt))
