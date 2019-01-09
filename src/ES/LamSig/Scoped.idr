module ES.LamSig.Typed

import Data.Fin

%access public export
%default total

mutual 
  data Term : Nat -> Type where
    Var  : Fin n -> Term n
    Lam  : Term (S n) -> Term n
    App  : Term n -> Term n -> Term n
    Clos : Term n -> Subs k n -> Term k

  data Subs : Nat -> Nat -> Type where
    Id    : Subs n n
    Shift : Subs (S n) n
    Cons  : Term n -> Subs n k -> Subs n (S k)
    Comp  : Subs n m -> Subs m k -> Subs n k