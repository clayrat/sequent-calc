module Lambda.STLC.NbE

import Lambda.STLC.Ty
import Data.List
import Data.List.Elem

%default total

infixr 5 ++<
(++<) : List a -> List a -> List a
xs ++< []      = xs
xs ++< (y::ys) = (y::xs) ++< ys

data Tm : List Ty -> Ty -> Type where
  Var :             Elem t g -> Tm g t
  Lam : {s : Ty} -> Tm (s::g) t -> Tm g (s~>t)
  App : {s : Ty} -> Tm g (s~>t) -> Tm g s -> Tm g t

-- semantics

IntTy : Ty -> Type
IntTy  A        = Nat
IntTy (Imp s t) = IntTy s -> IntTy t

IntCx : List Ty -> (Ty -> Type) -> Type
IntCx  []    _ = ()
IntCx (s::g) v = (IntCx g v, v s)

IntD : Elem t g -> IntCx g v -> v t
IntD  Here     (g, t) = t
IntD (There i) (g, s) = IntD i g

IntTm : Tm g t -> IntCx g IntTy -> IntTy t
IntTm (Var i)   g = IntD i g
IntTm (Lam t)   g = \s => IntTm t (g, s)
IntTm (App f s) g = IntTm f g (IntTm s g)

-- substitution

Ren : List Ty -> List Ty -> Type
Ren g d = forall t. Elem t g -> Elem t d

wkr : Ren g d -> Ren (s::g) (s::d)
wkr r  Here      = Here
wkr r (There el) = There (r el)

weak : (k : List Ty) -> Ren g (g++<k)
weak []      el = el
weak (q::qs) el = weak qs (There el)

rename : Ren g d -> Tm g a -> Tm d a
rename r (Var el)    = Var $ r el
rename r (Lam t)     = Lam $ rename (wkr r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)

Sub : List Ty -> List Ty -> Type
Sub g d = forall t. Elem t g -> Tm d t

wks : Sub g d -> Sub (s::g) (s::d)
wks s  Here      = Var Here
wks s (There el) = rename There (s el)

sub : Sub g d -> Tm g a -> Tm d a
sub s (Var el)    = s el
sub s (Lam t)     = Lam $ sub (wks s) t
sub s (App t1 t2) = App (sub s t1) (sub s t2)

-- NbE

mutual
  data NF : List Ty -> Ty -> Type where
    LamN : NF (s::g) t -> NF g (s~>t)
    AppN : Elem t g -> Spi g t -> NF g A

  data Spi : List Ty -> Ty -> Type where
    Nil  : Spi g A
    Cons : NF g s -> Spi g t -> Spi g (s~>t)

mutual
  renNm : Ren g d -> NF g t -> NF d t
  renNm r (LamN n)   = LamN (renNm (wkr r) n)
  renNm r (AppN v s) = AppN (r v) (renSp r s)

  renSp : Ren g d -> Spi g t -> Spi d t
  renSp r  Nil       = Nil
  renSp r (Cons n s) = Cons (renNm r n) (renSp r s)

mutual
  eta1 : {s : Ty} -> Elem s g -> NF g s
  eta1 v = eta $ \d => AppN (weak d v)

  eta : {s : Ty} -> ((d : List Ty) -> Spi (g++<d) s -> NF (g++<d) A) -> NF g s
  eta {s=A}       c = c [] Nil
  eta {s=Imp s t} c = LamN $ eta $ \d, sp => c (s :: d) (Cons (eta1 (weak d Here)) sp)

data Stop : List Ty -> Ty -> Type where
  VarS : Elem t g -> Stop g t
  AppS : Stop g (s~>t) -> NF g s -> Stop g t

renSt : Ren g d -> Stop g t -> Stop d t
renSt r (VarS x)   = VarS (r x)
renSt r (AppS s n) = AppS (renSt r s) (renNm r n)

stopSp : Stop g t -> Spi g t -> NF g A
stopSp (VarS x)   ss = AppN x ss
stopSp (AppS s n) ss = stopSp s (Cons n ss)

mutual
  Val : List Ty -> Ty -> Type
  Val g t = Either (Go g t) (Stop g t)

  Go : List Ty -> Ty -> Type
  Go g  A        = Void
  Go g (Imp s t) = forall d. Ren g d -> Val d s -> Val d t

renVal : (t : Ty) -> Ren g d -> Val g t -> Val d t
renVal  A        r (Left g)  = absurd g
renVal (Imp s t) r (Left g)  = Left $ \r',g' => g (r' . r) g'
renVal  t        r (Right s) = Right (renSt r s)

renVals : (ts : List Ty) -> Ren g d -> IntCx ts (Val g) -> IntCx ts (Val d)
renVals  []     r ()      = ()
renVals (t::ts) r (ti, v) = (renVals ts r ti, renVal t r v)

idEnv : (g : List Ty) -> IntCx g (Val g)
idEnv  []     = ()
idEnv (g::gs) = (renVals gs There (idEnv gs), Right $ VarS Here)

mutual
  applyVal : {s : Ty} -> Val g (Imp s t) -> Val g s -> Val g t
  applyVal (Left f)  v = f id v
  applyVal (Right f) v = Right $ AppS f (quoteVal s v)

  quoteVal : (t : Ty) -> Val g t -> NF g t
  quoteVal  A        (Left v)  = absurd v
  quoteVal (Imp s t) (Left v)  = LamN $ quoteVal t (v There (Right $ VarS Here))
  quoteVal  t        (Right v) = eta $ \d => stopSp (renSt (weak d) v)

eval : {g : List Ty} -> Tm g t -> IntCx g (Val d) -> Val d t
eval (Var  Here)      (gi, v) = v
eval (Var (There el)) (gi, v) = assert_total $ eval (Var el) gi   -- totality checker ugh
eval (Lam t)           gi     = Left $ \r, v => eval t (renVals g r gi, v)
eval (App t u)         gi     = applyVal (eval t gi) (eval u gi)

nbe : {g : List Ty} -> {t : Ty} -> Tm g t -> NF g t
nbe tm = quoteVal t (eval tm (idEnv g))

test : Tm [] (((A~>A)~>(A~>A))~>((A~>A)~>(A~>A)))
test = Lam $ Var Here

test2 : {t : Ty} -> Tm [] ((t~>t)~>(t~>t))
test2 = Lam $ Lam $ App (Var $ There Here) (App (Var $ There Here) (Var Here))
