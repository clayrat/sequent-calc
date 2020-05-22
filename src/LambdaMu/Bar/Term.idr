module LambdaMu.Bar.Term

import Data.List
import Elem
import Lambda.STLC.Ty

%access public export
%default total

-- lambda-bar-mu
-- weakening is implicit in var/covar
-- contraction is implicit in cons/cut

mutual
  data Term : List Ty -> Ty -> List Ty -> Type where
    Var : Elem a g -> Term g a d
    Lam : Term (a::g) b d -> Term g (a~>b) d
    Mu  : Cmd g (a::d) -> Term g a d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Cons  : Term g a d -> CoTerm g b d -> CoTerm g (a~>b) d

  data Cmd : List Ty -> List Ty -> Type where
    Cut : Term g a d -> CoTerm g a d -> Cmd g d
