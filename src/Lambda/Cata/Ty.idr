module Lambda.Cata.Ty

import Data.Fin
import Data.Vect

--%access public export
%default total

-- since we only have one kind, contexts collapse into nats
public export
data Ty : Nat -> Type where
  U    : Ty n
  TVar : Fin n -> Ty n
  Imp  : Ty Z -> Ty n -> Ty n
  Prod : Ty n -> Ty n -> Ty n
  Sum  : Ty n -> Ty n -> Ty n
  Mu   : Ty (S n) -> Ty n

infixr 5 ~>
public export
(~>) : Ty Z -> Ty n -> Ty n
(~>) = Imp

public export
RenT : Nat -> Nat -> Type
RenT n m = Fin n -> Fin m

public export
extT : RenT n m -> RenT (S n) (S m)
extT s  FZ    = FZ
extT s (FS x) = FS (s x)

public export
renameT : RenT n m -> Ty n -> Ty m
renameT r  U         = U
renameT r (TVar f)   = TVar $ r f
renameT r (Imp t u)  = Imp t (renameT r u)
renameT r (Prod t u) = Prod (renameT r t) (renameT r u)
renameT r (Sum t u)  = Sum (renameT r t) (renameT r u)
renameT r (Mu t)     = Mu $ renameT (extT r) t

export
weakenT : Ty n -> Ty (S n)
weakenT = renameT FS

public export
SubT : Nat -> Nat -> Type
SubT n m = Fin n -> Ty m

public export
extsT : SubT n m -> SubT (S n) (S m)
extsT s  FZ    = TVar FZ
extsT s (FS f) = renameT FS (s f)

public export
substT : SubT n m -> Ty n -> Ty m
substT s  U         = U
substT s (TVar f)   = s f
substT s (Imp t u)  = Imp t (substT s u)
substT s (Prod t u) = Prod (substT s t) (substT s u)
substT s (Sum t u)  = Sum (substT s t) (substT s u)
substT s (Mu t)     = Mu $ substT (extsT s) t

public export
SubNT : Vect n (Ty k) -> SubT n k
SubNT (t::ts)  FZ    = t
SubNT (t::ts) (FS n) = SubNT ts n

public export
substNT : Ty n -> Vect n (Ty k) -> Ty k
substNT b ns = substT (SubNT ns) b

public export
Sub1T : Ty n -> SubT (S n) n
Sub1T t  FZ    = t
Sub1T t (FS f) = TVar f

public export
subst1T : Ty (S n) -> Ty n -> Ty n
subst1T b a = substT (Sub1T a) b

export
subWeak : (t, u : Ty n) -> subst1T (weakenT t) u = t
subWeak  U         u = Refl
subWeak (TVar f)   u = Refl
subWeak (Imp t u)  v = cong (Imp t) $ subWeak u v
subWeak (Prod t u) v = rewrite subWeak t v in
                       rewrite subWeak u v in
                       Refl
subWeak (Sum t u)  v = rewrite subWeak t v in
                       rewrite subWeak u v in
                       Refl
subWeak (Mu t)     u = ?wat6

export
subCons : {a : Ty n} -> {as : Vect k (Ty n)} -> (t : Ty (S k)) ->
           subst1T (substT (extsT (SubNT as)) t) a = substNT t (a :: as)

export
sub0_1N : (r : Ty 1) -> (v : Ty 0) -> subst1T r v = substNT r [v]
