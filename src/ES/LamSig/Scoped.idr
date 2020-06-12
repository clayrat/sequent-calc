module ES.LamSig.Scoped

import Data.Fin

%default total

mutual
  public export
  data Term : Nat -> Type where
    Var  : Term n
    Lam  : Term (S n) -> Term n
    App  : Term n -> Term n -> Term n
    Clos : Term n -> Subs k n -> Term k

  public export
  data Subs : Nat -> Nat -> Type where
    Id    : Subs n n
    Shift : Subs (S n) n
    Cons  : Term n -> Subs n k -> Subs n (S k)
    Comp  : Subs n m -> Subs m k -> Subs n k