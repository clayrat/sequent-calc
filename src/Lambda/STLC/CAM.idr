module Lambda.STLC.CAM

import Data.List
import Data.List.Quantifiers
import Path
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  data Directive : List Ty -> List Ty -> List Ty -> Type where
    Id : Directive g d d
    Fst : Directive
    Snd : Directive
    Push : Directive
    Swap : Directive
    Cns : Directive
    Ap : Directive g ((a~>b)::a::d) (b::d)
    Quot : Value a -> Directive g d (a::d)
    Cur : Control -> Directive

  Control : List Ty -> List Ty -> List Ty -> Type
  Control g d t = Path (Directive g) d t

  data Value : Ty -> Type where
    NIL : Value a
    CLOS : Value a -> Control g d s -> Value a
    PAIR : Value a -> Value a -> Value a

Stack : List Ty -> Type
Stack = All Value

record State (a : Ty) where
  constructor St
  stack : Stack d
  control : Control g (t++d) [a]

  step : State a -> Maybe (State a)
  step (St                     s      (Id::p)) = Just $ St            s      p
  step (St          (PAIR e _::s)    (Fst::p)) = Just $ St        (e::s)     p
  step (St          (PAIR _ f::s)    (Snd::p)) = Just $ St        (f::s)     p
  step (St          (       _::s) (Quot f::p)) = Just $ St        (f::s)     p
  step (St          (       e::s)   (Push::p)) = Just $ St     (e::e::s)     p
  step (St          (    e::f::s)   (Swap::p)) = Just $ St     (f::e::s)     p
  step (St          (    e::f::s)    (Cns::p)) = Just $ St (PAIR f e::s)     p
  step (St          (       e::s)  (Cur q::p)) = Just $ St (CLOS e q::s)     p
  step (St (PAIR (CLOS e q) f::s)     (Ap::p)) = Just $ St (PAIR e f::s) (q++p)
  step  _                                      = Nothing
