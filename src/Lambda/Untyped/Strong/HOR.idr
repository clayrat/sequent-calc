module Lambda.Untyped.Strong.HOR

import Iter
import Lambda.Untyped.Term

%default total
%access public export

-- head-order reduction

mutual
  Env : Type
  Env = List (Either Clos Nat)

  data Clos = Cl Term Env

data Stor = L | A | T Term | C Clos

Stack : Type
Stack = List Stor

data State = Down Term Env Stack Nat
           |   Up Term     Stack Nat
           | Done Term

step : State -> Maybe State
step (Down (App t0 t1)                  e                 s     u ) = Just $ Down  t0                                  e  (C (Cl t1 e)::s)    u
step (Down (Lam t)                      e  (C (Cl t1 e1)::s)    u ) = Just $ Down  t                 (Left (Cl t1 e1)::e)               s     u
step (Down (Lam t)                      e                 s     u ) = Just $ Down  t                     (Right (S u)::e)           (L::s) (S u)
step (Down (Var (S i))              (_::e)                s     u ) = Just $ Down (Var i)                              e                s     u
step (Down (Var  Z)    (Left (Cl t e1)::e)                s     u ) = Just $ Down  t                                  e1                s     u
step (Down (Var  Z)          (Right u1::e)                s     u ) = Just $ Up   (Var (minus u u1))                                    s     u
step (Up     t                                        (L::s) (S u)) = Just $ Up   (Lam t)                                               s     u
step (Up    t1                                  (A::T t0::s)    u ) = Just $ Up   (App t0 t1)                                           s     u
step (Up    t0                             (C (Cl t1 e1)::s)    u ) = Just $ Down  t1                                 e1      (A::T t0::s)    u
step (Up     t                                           []     _ ) = Just $ Done  t
step  _                                                             = Nothing

runHOR : Term -> (Nat, State)
runHOR t = iterCount step (Down t [] [] 0)

test : Term
test = App (Lam $ Lam $ App (Var 1) (Var 0)) (Lam $ Var 0)
