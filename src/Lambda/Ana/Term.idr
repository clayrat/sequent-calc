module Lambda.Ana.Term

import Lambda.Ana.Ty
import Data.Fin
import Data.List
--import Data.Vect
import Data.List.Elem

--%access public export
%default total

-- isorecursive

public export
data Term : List (Ty n) -> Ty n -> Type where
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : {a : Ty 0} -> Term g (a~>b) -> Term g a -> Term g b
  Exf  : Term g V -> Term g a
  Pair : Term g a -> Term g b -> Term g (Prod a b)
  Fst  : Term g (Prod a b) -> Term g a
  Snd  : Term g (Prod a b) -> Term g b
  Inl  : Term g a -> Term g (Sum a b)
  Inr  : Term g b -> Term g (Sum a b)
  Case : {a, b : Ty n} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  Out  : Term g (Nu f) -> Term g (subst1T f (Nu f))
  Ana  : Term g (a ~> subst1T f a) -> Term g (a ~> Nu f)

UNIT : Ty n
UNIT = Nu $ TVar FZ

tt : Term {n=0} g UNIT
tt = App (Ana {a=V~>V} $ Lam $ Var Here) (Lam $ Var Here)

CONAT : Ty n
CONAT = Nu $ Sum UNIT (TVar FZ)

isZero : Term {n=0} g (CONAT ~> UNIT)
isZero = Ana $ Lam $ Var Here

pred : Term g (CONAT ~> CONAT)
pred = ?wat

STREAM : Ty (S n) -> Ty n
STREAM t = Nu $ Prod t (TVar FZ)
