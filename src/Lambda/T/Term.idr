module Lambda.T.Term

import Data.List

import Lambda.T.Ty

%default total
%access public export

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Zero : Term g N
  Succ : Term g N -> Term g N
  Rec  : Term g N -> Term g a -> Term g (a ~> N ~> a) -> Term g a
