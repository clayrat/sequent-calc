module ES.LamUps.Untyped

%hide Language.Reflection.App
%hide Interfaces.Abs
%access public export
%default total

mutual 
  data Term : Type where
    Abs  : Term -> Term
    Var  : Nat -> Term
    App  : Term -> Term -> Term
    Clos : Term -> Subs -> Term

  -- explicit substitutions 
  data Subs : Type where
    Lift  : Subs -> Subs
    Slash : Term -> Subs
    Shift : Subs

data Redex : Term -> Term -> Type where
  Beta     : Redex (App  (Abs a)      b       ) (Clos a (Slash b))
  AppR     : Redex (Clos (App a b)    s       ) (App (Clos a s) (Clos b s))
  Lambda   : Redex (Clos (Abs a)      s       ) (Abs (Clos a (Lift s)))
  FVar     : Redex (Clos (Var Z)     (Slash a))  a
  RVar     : Redex (Clos (Var (S n)) (Slash a)) (Var n)
  FVarLift : Redex (Clos (Var Z)     (Lift s) ) (Var Z)
  RVarLift : Redex (Clos (Var (S n)) (Lift s) ) (Clos (Clos (Var n) s) Shift)
  VarShift : Redex (Clos (Var n)      Shift   ) (Var (S n))
