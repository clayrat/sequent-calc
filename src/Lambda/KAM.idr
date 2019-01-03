module Lambda.KAM

import Data.List
import Subset

import Lambda.Ty
import Lambda.Lam

%default total
%access public export

-- untyped KAM 

mutual
  Env0 : Type 
  Env0 = List Clos0

  data Clos0 = Cl0 Tm0 Env0

Stack0 : Type
Stack0 = List Clos0

State0 : Type
State0 = (Tm0, Env0, Stack0)

step0 : State0 -> Maybe State0
step0 (Vr0  Z   , Cl0 t e::_,    s) = Just (    t,    e,          s)
step0 (Vr0 (S n),       _::e,    s) = Just (Vr0 n,    e,          s)
step0 (Lm0 t    ,          e, c::s) = Just (    t, c::e,          s)
step0 (Ap0 t u  ,          e,    s) = Just (    t,    e, Cl0 u e::s)
step0  _                            = Nothing

stepIter0 : State0 -> Maybe State0
stepIter0 s with (step0 s)
  | Nothing = Just s
  | Just s1 = assert_total $ stepIter0 s1

run0 : Tm0 -> Maybe State0
run0 t = stepIter0 (t, [], [])

test00 : run0 Term0 = Just (Lm0 $ Vr0 Z, [], [])
test00 = Refl

test01 : run0 Term1 = Just (Lm0 $ Vr0 Z, [], [])
test01 = Refl

test02 : run0 Term2 = Just (Lm0 $ Vr0 Z, [], [])
test02 = Refl

-- STLC KAM 

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Tm g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Clos a -> Stack b c -> Stack (Imp a b) c

record State (b : Ty) where
  constructor St 
  tm : Tm g a 
  env : Env g 
  stk : Stack a b 

step : State b -> Maybe (State b)
step (St (Vr  Here     ) (Cl t e0::_)       s ) = Just $ St  t          e0              s
step (St (Vr (There el))       (_::e)       s ) = Just $ St (Vr el)     e               s
step (St (Lm t         )           e  (CS c s)) = Just $ St  t      (c::e)              s
step (St (Ap t u       )           e        s ) = Just $ St  t          e  (Cl u e `CS` s)
step  _ = Nothing  

stepIter : State a -> (Nat, Maybe (State a))
stepIter s = loop Z s
  where
    loop : Nat -> State a -> (Nat, Maybe (State a))
    loop n s1 with (step s1)
      | Nothing = (n, Just s1)
      | Just s2 = assert_total $ loop (S n) s2

runKAM : Tm [] a -> (Nat, Maybe (State a))
runKAM t = stepIter $ St t [] NS

test1 : runKAM TestTm1 = (6, Just (St {g=[]} {a=TestTy} ResultTm [] NS))
test1 = Refl

test2 : runKAM TestTm2 = (6, Just (St {g=[]} {a=TestTy} ResultTm [] NS))
test2 = Refl

