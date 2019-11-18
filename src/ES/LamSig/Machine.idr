module ES.LamSig.Machine

import Data.Fin
import ES.LamSig.Untyped

%access public export
%default total

Stack : Type
Stack = List Term

record State where
  constructor St
  term : Term
  env  : Subs
  stk  : Stack

step : State -> Maybe State
step (St (Var  i)                         Shift                  s ) = Just $ St (Var (S i))        Id                     s
step (St (Var  Z)                        (Cons (Clos t e) _)     s ) = Just $ St  t                 e                      s
step (St (Var (S i))                     (Cons  _         e)     s ) = Just $ St (Var i)            e                      s
step (St (Var  i)                        (Comp e0 e1)            s ) = Just $ St (Clos (Var i) e0)  e1                     s
step (St (App t1 t2)                      e                      s ) = Just $ St  t1                e          (Clos t2 e::s)
step (St (Lam t)                          e                  (c::s)) = Just $ St  t                (Cons c e)              s
step (St (Clos (Var  i)     Id)           e                      s ) = Just $ St (Var  i)           e                      s
step (St (Clos (Var  i)     Shift)        e                      s ) = Just $ St (Var (S i))        e                      s
step (St (Clos (Var  Z)    (Cons t _))    e                      s ) = Just $ St  t                 e                      s
step (St (Clos (Var (S i)) (Cons _ e1))   e                      s ) = Just $ St (Clos (Var i) e1)  e                      s
step (St (Clos (Var  i)    (Comp e1 e2))  e                      s ) = Just $ St (Clos (Var i) e1) (Comp e2 e)             s
step (St (Clos  t           e1)           e                      s ) = Just $ St  t                (Comp e1 e)             s
step  _                                                              = Nothing

record StateS where
  constructor StS
  depth : Nat
  term : Term
  env  : Subs
  stk  : Stack

stepStr : StateS -> Maybe StateS
stepStr (StS    n  (Var  i)                         Shift                  s ) = Just $ StS    n  (Var (S i))        Id                                        s
stepStr (StS    n  (Var  Z)                        (Cons (Clos t e) _)     s ) = Just $ StS    n   t                 e                                         s
stepStr (StS    n  (Var (S i))                     (Cons  _         e)     s ) = Just $ StS    n  (Var i)            e                                         s
stepStr (StS    n  (Var  i)                        (Comp e0 e1)            s ) = Just $ StS    n  (Clos (Var i) e0)  e1                                        s
stepStr (StS    n  (App t1 t2)                      e                      s ) = Just $ StS    n  t1                e                             (Clos t2 e::s)
stepStr (StS    n  (Lam t)                          e                  (c::s)) = Just $ StS    n   t                (Cons c e)                                 s
stepStr (StS    n  (Clos (Var  i)     Id)           e                      s ) = Just $ StS    n  (Var  i)           e                                         s
stepStr (StS    n  (Clos (Var  i)     Shift)        e                      s ) = Just $ StS    n  (Var (S i))        e                                         s
stepStr (StS    n  (Clos (Var  Z)    (Cons t _))    e                      s ) = Just $ StS    n   t                 e                                         s
stepStr (StS    n  (Clos (Var (S i)) (Cons _ e1))   e                      s ) = Just $ StS    n  (Clos (Var i) e1)  e                                         s
stepStr (StS    n  (Clos (Var  i)    (Comp e1 e2))  e                      s ) = Just $ StS    n  (Clos (Var i) e1) (Comp e2 e)                                s
stepStr (StS    n  (Clos  t           e1)           e                      s ) = Just $ StS    n   t                (Comp e1 e)                                s
stepStr (StS    n  (Lam t)                          e                      []) = Just $ StS (S n)  t                (Cons (Var 0) (Comp e Shift))             []
--stepStr (St (Var i) e s) = ?wat
stepStr _ = Nothing

extractStr : StateS -> Term
extractStr (StS n t _ _) = lams n t
  where
  lams : Nat -> Term -> Term
  lams Z     t = t
  lams (S n) t = lams n (Lam t)

test : Term
test = App (Lam $ Lam $ App (Var 1) (Var 0)) (Lam $ Var 0)

zero : Term
zero = Lam $ Lam $ Var 1

succ : Term
succ = Lam $ Lam $ Lam $ App (Var 0) (Var 2)

one : Term
one = App succ zero

zero' : Term
zero' = Lam $ Lam $ Var 0

one' : Term
one' = Lam $ Lam $ App (Var 1) (Var 0)

succ' : Term
succ' = Lam $ Lam $ Lam $ App (Var 1) (App (App (Var 2) (Var 1)) (Var 0))
