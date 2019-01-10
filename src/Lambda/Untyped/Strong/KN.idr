module Lambda.Untyped.Strong.KN

import Util
import Lambda.Untyped.Term

%default total
%access public export

data Mark = Mk Term Nat -- portion of the normal form already built and its λ-nesting level

data TermN = T Term | V Nat | M Mark

mutual
  Env : Type 
  Env = List Clos

  data Clos = Cl TermN Env

data Stor = L | MM Mark | C Clos  

Stack : Type
Stack = List Stor

data State = More TermN Env Stack Nat
           | Done Term

init : Term -> State 
init t = More (T t) [] [] Z

step : State -> Maybe State                 
step (More (T (App t1 t2))           e                  s  m) = Just $ More (T t1)                                         e  (C (Cl (T t2) e)::s)    m
step (More (T (Lam t))               e            (C c::s) m) = Just $ More (T t)                                      (c::e)                   s     m
step (More (T (Lam t))               e                  s  m) = Just $ More (T t)                        (Cl (V (S m)) []::e)               (L::s) (S m)
step (More (T (Var  Z))    (Cl t e1::_)                 s  m) = Just $ More    t                                           e1                   s     m
step (More (T (Var (S n)))       (_::e)                 s  m) = Just $ More (T $ Var n)                                    e                    s     m
step (More (V  n)                    e                  s  m) = Just $ More (M $ Mk (Var $ minus m n) m)                   e                    s     m
step (More (M (Mk t _))              _                 []  _) = Just $ Done    t
step (More (M (Mk t n))              e   (C (Cl t1 e1)::s) _) = Just $ More    t1                                          e1     (MM (Mk t n)::s)    n
step (More (M (Mk t n))              e              (L::s) m) = Just $ More (M $ Mk (Lam t) n)                             e                    s     m
step (More (M (Mk t n))              e  (MM (Mk t1 n1)::s) m) = Just $ More (M $ Mk (App t1 t) n1)                         e                    s     m
step  _ = Nothing

test : Term
test = App (Lam $ Lam $ Lam $ App (Var 2) (Var 1)) (Lam $ App (Var 0) (Var 0))