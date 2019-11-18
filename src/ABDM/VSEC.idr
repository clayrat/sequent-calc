module ABDM.VSEC

import Iter
import Lambda.Untyped.Term

%default total
%access public export

data I = Access Nat
       | Close (List I)
       | Call

compile : Term -> List I
compile (Var n)   = [Access n]
compile (Lam t)   = [Close (compile t)]
compile (App t u) = compile u ++ compile t ++ [Call]

mutual
  Env : Type
  Env = List Clos

  data Clos = Cl (List I) Env

Stack : Type
Stack = List Clos

State : Type
State = (Stack, Env, List I)

step : State -> Maybe State
step (             s, e, Access i::c) = (\x=>(      x::s,    e ,     c)) <$> index' i e
step (             s, e, Close c1::c) = Just (Cl c1 e::s,    e ,     c)
step (Cl c1 e1::v::s, e,     Call::c) = Just (         s, v::e1, c1++c)
step _                                = Nothing

runVSEC : Term -> (Nat, State)
runVSEC t = iterCount step ([], [], compile t)
