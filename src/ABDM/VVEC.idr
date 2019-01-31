module ABDM.VVEC

import Iter

%default total
%access public export

data Literal = N Nat
             | B Bool

data Term = Var Nat
          | LamV Term
          | LamN Term
          | App Term Term
          | Lit Literal
          | Succ Term
          | If Term Term Term

data I = PushClos (List I)
       | PushConst Literal 
       | Call
       | Return 
       | Push Nat
       | Bind 
       | Incr
       | Test (List I) (List I)

compile : Term -> List I
compile (Var k)    = [Push k]
compile (LamV t)   = [PushClos $ Call :: Bind :: compile t ++ [Return]]
compile (LamN t)   = [PushClos $ Bind :: compile t ++ [Return]]
compile (App t u)  = PushClos (compile u ++ [Return]) :: compile t ++ [Call]
compile (Lit l)    = [PushConst l]
compile (Succ t)   = compile t ++ [Incr]
compile (If p t f) = compile p ++ [Test (compile t) (compile f)]

mutual
  Env : Type 
  Env = List Val

  data Val = Cl (List I) Env | L Literal

State : Type
State = (List Val, List Env, List I)  

step : State -> Maybe State
step (             vs, e::es, PushClos c1::c) = Just (    Cl c1 e::vs,      e::es,     c)
step (             vs,    es, PushConst l::c) = Just (        L l::vs,         es,     c)
step (    Cl c1 e::vs,    es,        Call::c) = Just (             vs,      e::es, c1++c)
step (             vs, _::es,      Return::c) = Just (             vs,         es,     c)
step (             vs, e::es,      Push n::c) = (\x => 
                                        case x of 
                                         L pv     => (       L pv::vs,      e::es,     c)
                                         Cl c1 e1 => (             vs,  e1::e::es, c1++c)
                                        ) <$> index' n e
step (          v::vs, e::es,        Bind::c) = Just (             vs, (v::e)::es,     c)
step (    L (N m)::vs,    es,        Incr::c) = Just (L (N (S m))::vs,         es,     c)
step ( L (B True)::vs,    es,   Test c1 _::c) = Just (             vs,         es, c1++c)
step (L (B False)::vs,    es,   Test _ c2::c) = Just (             vs,         es, c2++c)
step _                                        = Nothing
