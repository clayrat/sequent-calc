module Lambda.STLC.LAM1

import Data.List
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- Leroy Abstract Machine, right-to-left call-by-value

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)

  data Clos : Ty -> Type where
    Cl : Term g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c
  Fun : Clos (a~>b) -> Stack b c -> Stack a c

data State : Ty -> Type where
  L : Term g a -> Env g -> Stack a b -> State b
  R : Clos a -> Stack a b -> State b

step : State a -> Maybe (State a)
step (L (Var  Here)      (v::_)                 s ) = Just $ R  v                                s
step (L (Var (There el)) (_::e)                 s ) = Just $ L (Var el)         e                s
step (L (App t u)            e                  s ) = Just $ L  u               e  (Fun (Cl t e) s)
step (L (Lam t)              e                  s ) = Just $ R (Cl (Lam t)      e)               s
step (R (Cl  t               e) (Fun (Cl t1 e1) s)) = Just $ L  t1              e1 (Arg (Cl t e) s)
step (R (Cl (Lam t)          e)         (Arg cl s)) = Just $ L  t          (cl::e)               s
step  _                                             = Nothing

runLAM : Term [] a -> (Nat, State a)
runLAM t = iterCount step $ L t [] Mt

private
test1 : runLAM TestTm1 = (11, R (Cl ResultTm []) Mt)
test1 = Refl

private
test2 : runLAM TestTm2 = (11, R (Cl ResultTm []) Mt)
test2 = Refl
