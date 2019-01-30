module ABDM.VCAM

import Iter

%default total
%access public export

data Term = Var Nat
          | Lam Term
          | App Term Term
          | Nil
          | Cons Term Term
          | Car Term
          | Cdr Term

mutual           
  data Val = Null | Pair Val Val | Cl Val (List I)

  data I = Fst 
         | Snd 
         | Push 
         | Swap 
         | Cns  
         | Call 
         | Cur (List I) 
         | Quote Val

compile : Term -> List I
compile (Var Z)     = [Snd]
compile (Var (S n)) = Fst :: (assert_total $ compile (Var n))
compile (Lam t)     = [Cur (compile t)]
compile (App t u)   = Push :: (compile t) ++ Swap :: compile u ++ [Cns, Call]         
compile  Nil        = [Quote Null]
compile (Cons t u)  = Push :: (compile t) ++ Swap :: compile u ++ [Cns]
compile (Car t)     = compile t ++ [Fst]
compile (Cdr t)     = compile t ++ [Snd]

Stack : Type
Stack = List Val

State : Type
State = (List I, Val, Stack)

step : State -> Maybe State
step (    Fst::c,         Pair v1 _,     s) = Just (    c,        v1,    s)
step (    Snd::c,         Pair _ v2,     s) = Just (    c,        v2,    s)
step (Quote v::c,                 _,     s) = Just (    c,         v,    s)
step ( Cur c1::c,                 v,     s) = Just (    c,   Cl v c1,    s)
step (   Push::c,                 v,     s) = Just (    c,         v, v::s)
step (   Swap::c,                 v, v1::s) = Just (    c,        v1, v::s)
step (    Cns::c,                 v, v1::s) = Just (    c, Pair v1 v,    s)
step (   Call::c, Pair (Cl v c1) v1,     s) = Just (c1++c, Pair v v1,    s)
step  _                                     = Nothing