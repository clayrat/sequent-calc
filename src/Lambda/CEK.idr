module Lambda.CEK

import Data.List
import Subset

import Lambda.Ty
import Lambda.Lam

%default total
%access public export

-- untyped CEK

mutual
  Env0 : Type 
  Env0 = List Clos0

  data Clos0 = Cl0 Tm0 Env0

data Frame0 = Fun0 Tm0 Env0 | Arg0 Clos0

Stack0 : Type
Stack0 = List Frame0

data State0 = L0 Tm0 Env0 Stack0 | R0 Clos0 Stack0

step0 : State0 -> Maybe State0
step0 (L0 (Vr0  Z)    (v::_)              s ) = Just $ R0  v                                     s
step0 (L0 (Vr0 (S n)) (_::e)              s ) = Just $ L0 (Vr0 n)      e                         s
step0 (L0 (Lm0 t)         e               s ) = Just $ R0 (Cl0 (Lm0 t) e)                        s
step0 (L0 (Ap0 t u)       e               s ) = Just $ L0 u            e              (Fun0 t e::s)
step0 (R0 (Cl0 (Lm0 t)    e) (Fun0 t1 e1::s)) = Just $ L0 t1           e1 (Arg0 (Cl0 (Lm0 t) e)::s)
step0 (R0 (Cl0 (Lm0 t)    e) (    Arg0 v::s)) = Just $ L0 t        (v::e)                        s
step0 _ = Nothing

stepIter0 : State0 -> (Nat, Maybe State0)
stepIter0 s = loop0 Z s
  where
    loop0 : Nat -> State0 -> (Nat, Maybe State0)
    loop0 n s1 with (step0 s1)
      | Nothing = (n, Just s1)
      | Just s2 = assert_total $ loop0 (S n) s2

run0 : Tm0 -> (Nat, Maybe State0)
run0 t = stepIter0 $ L0 t [] []

test00 : run0 Term0 = (11, Just (R0 (Cl0 (Lm0 (Vr0 0)) []) []))
test00 = Refl

test01 : run0 Term1 = (11, Just (R0 (Cl0 (Lm0 (Vr0 0)) []) []))
test01 = Refl

test02 : run0 Term2 = (11, Just (R0 (Cl0 (Lm0 (Vr0 0)) []) []))
test02 = Refl

-- STLC CEK 
{-
mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Tm g a -> Env g -> Clos a

data Frame : Ty -> Type where
  Fun : Tm g a -> Env g -> Frame a
  Arg : Clos a -> Frame a
 
data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Frame a -> Stack b c -> Stack (Imp a b) c

--data Stack : Ty -> Ty -> Type where
--  NS : Stack a a
--  FS : Tm g a -> Env g -> Stack b c -> Stack a c
--  AS : Clos a -> Stack b c -> Stack a c

data State : List Ty -> Ty -> Ty -> Type where
  L : Tm g a -> Env g -> Stack a b -> State g a b
  R : Clos a -> Stack a b -> State g a b

step : State g a b -> Maybe (d ** c ** h ** State d c h)
step {g=a::g}             {b} (L (Vr  Here)      (v::_)                 s ) = Just (   g ** a ** b   ** R  v            s)
step {g=_::g} {a}         {b} (L (Vr (There el)) (_::e)                 s ) = Just (   g ** a ** b  ** L (Vr el)    e  s)
step {g}      {a=Imp a x} {b} (L (Lm t)              e                  s ) = Just (   g ** Imp a x ** b ** R (Cl (Lm t) e) s)
step {g}      {a}         (L (Ap {a=x} t u)      e                  s ) = Just (   g ** x  ** b     ** L  u         e  ?wat)
step          {a=Imp a x} (R (Cl       (Lm t)    e) (CS (Fun {g=j} t1 e1) s)) = ?wat4 --Just (   j ** a       ** L t1         e1 ?wat1)
step {g}      {a=Imp a x} (R (Cl {g=j} (Lm t)    e) (CS (Arg v)           s)) = ?wat5 --Just (a::j ** x       ** L t      (v::e) s)
step _ = Nothing
-}
