module Lambda.Cata.Term

import Lambda.Cata.Ty
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
  TT   : Term g U
  Pr   : Term g a -> Term g b -> Term g (Prod a b)
  Fst  : {b : Ty n} -> Term g (Prod a b) -> Term g a
  Snd  : {a : Ty n} -> Term g (Prod a b) -> Term g b
  Inl  : Term g a -> Term g (Sum a b)
  Inr  : Term g b -> Term g (Sum a b)
  Case : {a, b : Ty n} -> Term g (Sum a b) -> Term (a::g) c -> Term (b::g) c -> Term g c
  In   : Term g (subst1T f (Mu f)) -> Term g (Mu f)
  Ni   : {f : Ty (S n)} -> Term g (Mu f) -> Term g (subst1T f (Mu f))
  Cata : {f : Ty 1} -> Term g (subst1T f a ~> a) -> Term g (Mu f) -> Term g a

public export
BOOL : Ty Z
BOOL = Sum U U

export
true : Term g BOOL
true = Inl TT

export
false : Term g BOOL
false = Inr TT

export
ite : Term g (BOOL ~> a ~> a ~> a)
ite = Lam $ Lam $ Lam $ Case (Var $ There $ There Here) (Var $ There $ There Here) (Var $ There Here)

public export
NAT : Ty Z
NAT = Mu $ Sum U (TVar FZ)

export
zero : Term g NAT
zero = In $ Inl TT

export
succ : Term g (NAT ~> NAT)
succ = Lam $ In $ Inr $ Var Here

export
pred : Term g (NAT ~> Sum U NAT)
pred = Lam $ Ni $ Var Here

export
add : Term g (NAT~>NAT~>NAT)
add = Lam $ Lam $ Cata (Lam $ Case (Var Here) (Var $ There $ There Here) (In $ Inr $ Var Here)) (Var $ There Here)

public export
LIST : Ty n -> Ty n
LIST t = Mu $ Sum U (Prod (weakenT t) (TVar FZ))

export
nil : Term g (LIST t)
nil = In $ Inl TT

export
cons : Term g t -> Term g (LIST t) -> Term g (LIST t)
cons hd tl = In $ Inr $ Pr (rewrite subWeak t (LIST t) in hd) tl

export
head : {t : Ty 0} -> Term g (LIST t ~> Sum U t)
head = Lam $ Case (Ni $ Var Here) (Inl $ Var Here) (Inr $ Fst $ rewrite subWeak t (LIST t) in Var Here)

export
tail : {t : Ty 0} -> Term g (LIST t ~> Sum U (LIST t))
tail = Lam $ Case (Ni $ Var Here) (Inl $ Var Here) (Inr $ Snd $ rewrite subWeak t (LIST t) in Var Here)

export
append : {t : Ty 0} -> Term g (LIST t ~> LIST t ~> LIST t)
append = Lam $ Lam $ Cata (Lam $ Case (Var Here) (Var $ There $ There Here) (In $ Inr $ Var Here))
                          (Var $ There Here)

export
length : {t : Ty 0} -> Term g (LIST t ~> NAT)
length = Lam $ Cata (Lam $ Case (Var Here) zero (App succ (Snd $ Var Here)))
                    (Var Here)

export
l123 : Term g (LIST NAT)
l123 = cons (App succ zero) $
       cons (App succ $ App succ zero) $
       cons (App succ $ App succ $ App succ zero) $
       nil

-- interleaving
FIN : Ty Z
FIN = Mu $ Mu $ Sum U (Prod (TVar $ FS FZ) (TVar FZ))

VOID : Ty n
VOID = Mu $ TVar FZ

exfalso : Term {n=0} g (VOID ~> a)
exfalso = Lam $ Cata (Lam $ Var Here) (Var Here)
