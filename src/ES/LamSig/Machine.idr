module ES.LamSig.Machine

import Data.Fin
import Util
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

data Result a = More a | Done a | Fail

iterR : (a -> Result a) -> a -> Result a
iterR step = loop 
  where 
  loop : a -> Result a
  loop t = case step t of
    Fail => Done t
    Done t => Done t
    More t2 => assert_total $ loop t2

stepStr : State -> Result State
stepStr (St (Var  i)                         Shift                  s ) = More $ St (Var (S i))        Id                     s
stepStr (St (Var  Z)                        (Cons (Clos t e) _)     s ) = More $ St  t                 e                      s
stepStr (St (Var (S i))                     (Cons  _         e)     s ) = More $ St (Var i)            e                      s
stepStr (St (Var  i)                        (Comp e0 e1)            s ) = More $ St (Clos (Var i) e0)  e1                     s
stepStr (St (App t1 t2)                      e                      s ) = More $ St  t1                e          (Clos t2 e::s)
stepStr (St (Lam t)                          e                  (c::s)) = More $ St  t                (Cons c e)              s
stepStr (St (Clos (Var  i)     Id)           e                      s ) = More $ St (Var  i)           e                      s
stepStr (St (Clos (Var  i)     Shift)        e                      s ) = More $ St (Var (S i))        e                      s
stepStr (St (Clos (Var  Z)    (Cons t _))    e                      s ) = More $ St  t                 e                      s
stepStr (St (Clos (Var (S i)) (Cons _ e1))   e                      s ) = More $ St (Clos (Var i) e1)  e                      s
stepStr (St (Clos (Var  i)    (Comp e1 e2))  e                      s ) = More $ St (Clos (Var i) e1) (Comp e2 e)             s
stepStr (St (Clos  t           e1)           e                      s ) = More $ St  t                (Comp e1 e)             s

stepStr (St (Lam t) e []) = 
  case assert_total $ iterR stepStr (St t (Cons (Var 0) (Comp e Shift)) []) of
    More (St t1 e1 s1) => Done $ St (Lam t1) e1 s1 
    Done (St t1 e1 s1) => Done $ St (Lam t1) e1 s1 
    Fail => Fail
--stepStr (St (Var i) e s) = ?wat
stepStr  _                                                              = Fail

test : Term
test = App (Lam $ Lam $ App (Var 1) (Var 0)) (Lam $ Var 0)