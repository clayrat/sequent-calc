module ES.LamSig.Untyped

%default total

mutual
  public export
  data Term : Type where
    Var  : Term
    Lam  : Term -> Term
    App  : Term -> Term -> Term
    Clos : Term -> Subs -> Term

  public export
  data Subs : Type where
    Id    : Subs
    Shift : Subs
    Cons  : Term -> Subs -> Subs
    Comp  : Subs -> Subs -> Subs