module Lambda.Untyped.CAM2

import Iter
import Lambda.Untyped.Term

%default total
%access public export

mutual
  data Directive = Id
                 | Fst
                 | Snd
                 | Push
                 | Swap
                 | Cns
                 | Ap
                 | Quot Val
                 | Cur Control

  Control : Type
  Control = List Directive

  data Val = Null | Pair Val Val | Cl Val Control

Stack : Type
Stack = List Val

record State where
  constructor St
  stack : Stack
  control : Control

step : State -> Maybe State
step (St                   s      (Id::p)) = Just $ St            s      p
step (St        (Pair e _::s)    (Fst::p)) = Just $ St        (e::s)     p
step (St        (Pair _ f::s)    (Snd::p)) = Just $ St        (f::s)     p
step (St               (_::s) (Quot f::p)) = Just $ St        (f::s)     p
step (St               (e::s)   (Push::p)) = Just $ St     (e::e::s)     p
step (St            (e::f::s)   (Swap::p)) = Just $ St     (f::e::s)     p
step (St            (e::f::s)    (Cns::p)) = Just $ St (Pair f e::s)     p
step (St               (e::s)  (Cur q::p)) = Just $ St   (Cl e q::s)     p
step (St (Pair (Cl e q) f::s)     (Ap::p)) = Just $ St (Pair e f::s) (q++p)
step  _                                    = Nothing

compileNat : Nat -> Control
compileNat  Z    = [Snd]
compileNat (S n) = Fst :: compileNat n

compile : Term -> Control
compile (Var n)   = compileNat n
compile (Lam t)   = [Cur (compile t)]
compile (App t u) = Push :: compile t ++ Swap :: compile u ++ [Cns, Ap]

runCAM2 : Term -> (Nat, State)
runCAM2 t = iterCount step $ St [Null] (compile t)
