module Lambda.T.Iter.Term

import Data.List
import Lambda.T.Iter.Ty

%default total
%access public export

data Term : List Ty -> Ty -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Pair : Term g a -> Term g b -> Term g (Prod a b)
  Fst  : Term g (Prod a b) -> Term g a
  Snd  : Term g (Prod a b) -> Term g b
  Zero : Term g N
  Succ : Term g N -> Term g N
  Iter : Term g N -> Term g a -> Term g (a ~> a) -> Term g a
