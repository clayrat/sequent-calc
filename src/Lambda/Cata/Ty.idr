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
{-
export
substTComp : (snm : SubT n m) -> (smp : SubT m p) -> (t : Ty n) -> substT smp (substT snm t) = substT (substT smp . snm) t
substTComp snm smp  U         = Refl
substTComp snm smp (TVar f)   = Refl
substTComp snm smp (Imp t u)  =
  rewrite substTComp snm smp u in
  Refl
substTComp snm smp (Prod t u) =
  rewrite substTComp snm smp t in
  rewrite substTComp snm smp u in
  Refl
substTComp snm smp (Sum t u)  =
  rewrite substTComp snm smp t in
  rewrite substTComp snm smp u in
  Refl
substTComp snm smp (Mu t)     = ?wat0
  --rewrite substTComp (extsT snm) (extsT smp) t in
  --believe_me Refl
  -}
public export
Sub1T : Ty n -> SubT (S n) n
Sub1T a  FZ    = a
Sub1T a (FS f) = TVar f

public export
subst1T : Ty (S n) -> Ty n -> Ty n
subst1T b a = substT (Sub1T a) b

public export
SubNT : Vect n (Ty k) -> SubT n k
SubNT (t::ts)  FZ    = t
SubNT (t::ts) (FS n) = SubNT ts n

public export
substNT : Ty n -> Vect n (Ty k) -> Ty k
substNT b ns = substT (SubNT ns) b

export
sub0_1N : (r : Ty 1) -> (v : Ty 0) -> subst1T r v = substNT r [v]
sub0_1N  U          v = Refl
sub0_1N (TVar FZ)   v = Refl
sub0_1N (Imp t u)   v = cong (Imp t) $ sub0_1N u v
sub0_1N (Prod t u)  v = rewrite sub0_1N t v in cong (Prod (substNT t [v])) $ sub0_1N u v
sub0_1N (Sum t u)   v = rewrite sub0_1N t v in cong (Sum (substNT t [v])) $ sub0_1N u v
sub0_1N (Mu t)      v = ?wat01N
