module ES.LamSig.Typed

import Lambda.STLC.Ty
import Data.List

%hide Language.Reflection.App
%hide Interfaces.Abs
%access public export
%default total

mutual 
  data Term : List Ty -> Ty -> Type where
    Var  : Elem a g -> Term g a 
    Lam  : Term (a::g) b -> Term g (a~>b)
    App  : Term g (a~>b) -> Term g a -> Term g b
    Clos : Term g a -> Subs d g -> Term d a

  data Subs : List Ty -> List Ty -> Type where
    Id    : Subs g g 
    Shift : Subs (a::g) g
    Cons  : Term g a -> Subs g d -> Subs g (a::d)
    Comp  : Subs g e -> Subs e d -> Subs g d