module ES.LamSig.Typed

%access public export
%default total

mutual 
  data Term : Type where
    Var  : Nat -> Term
    Lam  : Term -> Term 
    App  : Term -> Term -> Term
    Clos : Term -> Subs -> Term 

  data Subs : Type where
    Id    : Subs 
    Shift : Subs 
    Cons  : Term -> Subs -> Subs
    Comp  : Subs -> Subs -> Subs