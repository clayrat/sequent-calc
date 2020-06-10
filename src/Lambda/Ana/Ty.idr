module Lambda.Ana.Ty

import Data.Fin
import Data.Vect

--%access public export
%default total

-- since we only have one kind, contexts collapse into nats
public export
data Ty : Nat -> Type where
  V    : Ty n
  TVar : Fin n -> Ty n
  Imp  : Ty Z -> Ty n -> Ty n
  Prod : Ty n -> Ty n -> Ty n
  Sum  : Ty n -> Ty n -> Ty n
  Nu   : Ty (S n) -> Ty n

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
renameT r  V         = V
renameT r (TVar f)   = TVar $ r f
renameT r (Imp t u)  = Imp t (renameT r u)
renameT r (Prod t u) = Prod (renameT r t) (renameT r u)
renameT r (Sum t u)  = Sum (renameT r t) (renameT r u)
renameT r (Nu t)     = Nu $ renameT (extT r) t

weaken : Ty n -> Ty (S n)
weaken = renameT FS

public export
SubT : Nat -> Nat -> Type
SubT n m = Fin n -> Ty m

public export
extsT : SubT n m -> SubT (S n) (S m)
extsT s  FZ    = TVar FZ
extsT s (FS f) = renameT FS (s f)

public export
substT : SubT n m -> Ty n -> Ty m
substT s  V         = V
substT s (TVar f)   = s f
substT s (Imp t u)  = Imp t (substT s u)
substT s (Prod t u) = Prod (substT s t) (substT s u)
substT s (Sum t u)  = Sum (substT s t) (substT s u)
substT s (Nu t)     = Nu $ substT (extsT s) t

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
subCons : {a : Ty n} -> {as : Vect k (Ty n)} -> (t : Ty (S k)) ->
           subst1T (substT (extsT (SubNT as)) t) a = substNT t (a :: as)

export
sub0_1N : (r : Ty 1) -> (v : Ty 0) -> subst1T r v = substNT r [v]

{-
idN : {n : Nat} -> Vect n (Ty n)
idN {n=Z}   = []
idN {n=S n} = TVar FZ :: map weaken idN

Sub1T : {n : Nat} -> Ty n -> SubT (S n) n
Sub1T t = SubNT (t :: idN {n})

subSub : Sub1T {n=0} v = SubNT [v]
subSub = ?wat0

subCons  U         = Refl
subCons (TVar FZ)   = Refl
subCons (TVar f) = ?wat3
subCons (Imp t u)  = cong (Imp t) $ subCons u
subCons (Prod t u) =
  rewrite subCons {a} {as} t in
  rewrite subCons {a} {as} u in
  Refl
subCons (Sum t u)  =
  rewrite subCons {a} {as} t in
  rewrite subCons {a} {as} u in
  Refl
subCons (Mu t)     = ?wat4

sub0_1N r v = Refl

extsNT : (k : Nat) -> SubT n m -> SubT (k + n) (k + m)
extsNT  Z    s  f     = s f
extsNT (S k) s  FZ    = TVar FZ
extsNT (S k) s (FS f) = renameT FS $ extsNT k s f

exts1NT : (k : Nat) -> {i : Fin (S k)} -> extsNT {m=0} k (Sub1T v) i = extsNT k (SubNT [v]) i
exts1NT  Z    = ?wat
exts1NT (S k) = ?wat2

subEx1N : {k : Nat} -> (v : Ty 0) -> (t : Ty (S k))
        -> substT (rewrite plusCommutative 1 k in extsNT k (Sub1T v)) t = substT (rewrite plusCommutative 1 k in extsNT k (SubNT [v])) t
subEx1N v  U         = Refl
subEx1N v (TVar i)   = ?wat3
subEx1N v (Imp t u)  = cong (Imp t) $ subEx1N v u
subEx1N v (Prod t u) = rewrite subEx1N v t in
                       rewrite subEx1N v u in
                       Refl
subEx1N v (Sum t u)  = rewrite subEx1N v t in
                       rewrite subEx1N v u in
                       Refl
subEx1N v (Mu t)     = ?wat4 --cong Mu $ subEx1N {k=S k} v t

export
sub0_1N : (r : Ty 1) -> (v : Ty 0) -> subst1T r v = substNT r [v]
sub0_1N  U          v = Refl
sub0_1N (TVar FZ)   v = Refl
sub0_1N (Imp t u)   v = cong (Imp t) $ sub0_1N u v
sub0_1N (Prod t u)  v = rewrite sub0_1N t v in
                        rewrite sub0_1N u v in
                        Refl
sub0_1N (Sum t u)   v = rewrite sub0_1N t v in
                        rewrite sub0_1N u v in
                        Refl
sub0_1N (Mu t)      v = cong Mu $ subEx1N {f=extsT} v t

sub1Ren : (t : Ty n) -> subst1T (renameT FS t) x = t
sub1Ren  U         = Refl
sub1Ren (TVar f)   = Refl
sub1Ren (Imp t u)  = cong (Imp t) $ sub1Ren {x} u
sub1Ren (Prod t u) = rewrite sub1Ren {x} t in
                     rewrite sub1Ren {x} u in
                     Refl
sub1Ren (Sum t u)  = rewrite sub1Ren {x} t in
                     rewrite sub1Ren {x} u in
                     Refl
sub1Ren (Mu t)     = ?wat

SubNT0 : {a : Ty n} -> {as : Vect k (Ty n)} -> (f : Fin (S k)) ->
         substT (Sub1T a) (extsT (SubNT as) f) = SubNT (a :: as) f
SubNT0 FZ = Refl
SubNT0 {as=[]} (FS f) = absurd f
SubNT0 {as=b::as} (FS f) = rewrite sym $ SubNT0 {a=b} {as} f in ?wat1

--subs1T (substT (extsT (SubNT as)) y) (substNT (Mu y) bs)
--=
--substNT y (substNT (Mu y) bs :: as)
export
subCons : {a : Ty n} -> {as : Vect k (Ty n)} -> (t : Ty (S k)) ->
           subst1T (substT (extsT (SubNT as)) t) a = substNT t (a :: as)
subCons  U         = Refl
subCons (TVar FZ)   = Refl
subCons (TVar f) = ?wat3
subCons (Imp t u)  = cong (Imp t) $ subCons u
subCons (Prod t u) =
  rewrite subCons {a} {as} t in
  rewrite subCons {a} {as} u in
  Refl
subCons (Sum t u)  =
  rewrite subCons {a} {as} t in
  rewrite subCons {a} {as} u in
  Refl
subCons (Mu t)     = ?wat4
  -}