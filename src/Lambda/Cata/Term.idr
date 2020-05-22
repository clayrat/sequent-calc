module Lambda.Cata.Term

import Lambda.Cata.Ty
import Data.Fin
import Data.List

%access public export
%default total

data Term : List (Ty n) -> Ty n -> Type where
  TT   : Term g U
  Var  : Elem a g -> Term g a
  Lam  : Term (a::g) b -> Term g (a~>b)
  App  : Term g (a~>b) -> Term g a -> Term g b
  Pair : Term g a -> Term g b -> Term g (Prod a b)
  Fst  : Term g (Prod a b) -> Term g a
  Snd  : Term g (Prod a b) -> Term g b
  Inl  : Term g a -> Term g (Sum a b)
  Inr  : Term g b -> Term g (Sum a b)
  Case : Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  In   : Term g (subst1T f (Mu f)) -> Term g (Mu f)
  Cata : Term g (subst1T f a ~> a) -> Term g (Mu f ~> a)

NAT : Ty n
NAT = Mu $ Sum U (TVar FZ)

zero : Term g NAT
zero = In $ Inl TT

succ : Term {n=0} g (NAT ~> NAT)
succ = Lam $ In $ Inr $ Var Here

add : Term {n=0} g (NAT~>NAT~>NAT)
add = Lam $ Cata $ Lam $ Case (Var Here) (Var $ There $ There Here) (In $ Inr $ Var Here)

LISTNAT : Ty 0
LISTNAT = Mu $ Sum U (Prod NAT (TVar FZ))

l123 : Term g LISTNAT
l123 = In $ Inr $ Pair (In $ Inr $ In $ Inl TT) $
       In $ Inr $ Pair (In $ Inr $ In $ Inr $ In $ Inl TT) $
       In $ Inr $ Pair (In $ Inr $ In $ Inr $ In $ Inr $ In $ Inl TT) $
       In $ Inl TT

FIN : Ty 0
FIN = Mu $ Mu $ Sum U (Prod (TVar $ FS FZ) (TVar FZ))
