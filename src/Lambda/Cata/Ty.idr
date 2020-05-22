module Lambda.Cata.Ty

import Data.Fin

%access public export
%default total

-- since we only have one kind, contexts collapse into nats
data Ty : Nat -> Type where
  U    : Ty n
  TVar : Fin n -> Ty n
  Imp  : Ty Z -> Ty n -> Ty n
  Prod : Ty n -> Ty n -> Ty n
  Sum  : Ty n -> Ty n -> Ty n
  Mu   : Ty (S n) -> Ty n

infixr 5 ~>
(~>) : Ty Z -> Ty n -> Ty n
(~>) = Imp

RenT : Nat -> Nat -> Type
RenT n m = Fin n -> Fin m

extT : RenT n m -> RenT (S n) (S m)
extT s  FZ    = FZ
extT s (FS x) = FS (s x)

renameT : RenT n m -> Ty n -> Ty m
renameT r  U         = U
renameT r (TVar f)   = TVar $ r f
renameT r (Imp t u)  = Imp t (renameT r u)
renameT r (Prod t u) = Prod (renameT r t) (renameT r u)
renameT r (Sum t u)  = Sum (renameT r t) (renameT r u)
renameT r (Mu t)     = Mu $ renameT (extT r) t

SubT : Nat -> Nat -> Type
SubT n m = Fin n -> Ty m

extsT : SubT n m -> SubT (S n) (S m)
extsT s  FZ    = TVar FZ
extsT s (FS f) = renameT FS (s f)

substT : SubT n m -> Ty n -> Ty m
substT s  U         = U
substT s (TVar f)   = s f
substT s (Imp t u)  = Imp t (substT s u)
substT s (Prod t u) = Prod (substT s t) (substT s u)
substT s (Sum t u)  = Sum (substT s t) (substT s u)
substT s (Mu t)     = Mu $ substT (extsT s) t

Sub1T : Ty n -> SubT (S n) n
Sub1T a  FZ    = a
Sub1T a (FS f) = TVar f

subst1T : Ty (S n) -> Ty n -> Ty n
subst1T b a = substT (Sub1T a) b
