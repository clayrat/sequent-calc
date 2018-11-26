module ES.Defun

import Data.Fin

%access public export
%default total

mutual
  data Tm : Nat -> Type where
    Var : Fin n -> Tm n
    Lam : Tm (S n) -> Tm n
    App : Tm n -> Tm n -> Tm n
    Esb : Exp n -> Tm n

  record Exp (n : Nat) where
    constructor MkExp
    {len : Nat}
    et : Tm len
    es : Sub len n

  data Sub : Nat -> Nat -> Type where
    Rs   : Ren n o -> Sub m n -> Sub m o
    Ss   : Sub n o -> Sub m n -> Sub m o
    (::) : Tm n -> Sub m n -> Sub (S m) n
    Nil  : Sub 0 m
    I    : Sub m m
    Sw   : Sub m n -> Sub (S m) (S n)

  data Ren : Nat -> Nat -> Type where
    Up : Ren m (S m)
    Rw : Ren m n -> Ren (S m) (S n)

Clo : Type
Clo = Tm 0    

IntRen : Nat -> Nat -> Type
IntRen m n = Fin m -> Fin n

IntSub : Nat -> Nat -> Type
IntSub m n = Fin m -> Tm n

Hom : Nat -> Nat -> Type
Hom m n = Tm m -> Tm n

intRen : Ren m n -> IntRen m n
intRen  Up     i     = FS i
intRen (Rw _)  FZ    = FZ
intRen (Rw r) (FS i) = FS $ intRen r i

mutual 
  intSub : Sub m n -> IntSub m n
  intSub (Rs s t)  i     = intHomR s (intSub t i)
  intSub (Ss s t)  i     = assert_total $ intHomS s (intSub t i)
  intSub (e::_)  FZ    = e
  intSub (_::t) (FS i) = intSub t i
  intSub []        i     = absurd i
  intSub  I        i     = Var i
  intSub (Sw _)    FZ    = Var FZ 
  intSub (Sw s)   (FS i) = intHomR Up (intSub s i)
  
  intHomR : Ren m n -> Hom m n
  intHomR r (Var i)             = Var $ intRen r i
  intHomR r (Lam e)             = Lam $ intHomR (Rw r) e
  intHomR r (App e0 e1)         = App (intHomR r e0) (intHomR r e1)
  intHomR r (Esb (MkExp et es)) = Esb $ MkExp et (Rs r es)

  intHomS : Sub m n -> Hom m n
  intHomS s (Var i)             = intSub s i
  intHomS s (Lam e)             = Lam $ intHomS (Sw s) e
  intHomS s (App e0 e1)         = App (intHomS s e0) (intHomS s e1)
  intHomS s (Esb (MkExp et es)) = Esb $ MkExp et (Ss s es)

resolve : Tm m -> Tm m
resolve (Var i)             = Var i
resolve (Lam e)             = Lam $ resolve e
resolve (App e0 e1)         = App (resolve e0) (resolve e1)
resolve (Esb (MkExp et es)) = assert_total $ resolve $ intHomS es et

record Krivine (m : Nat) where
  constructor MkKAM
  head : Exp m
  args : List (Tm m)

into : Tm m -> Krivine m
into e = MkKAM (MkExp e I) []

from : Krivine m -> Maybe (Tm m)
from (MkKAM (MkExp (Lam e) es) []) = Just $ Esb $ MkExp (Lam e) es
from (MkKAM (MkExp (Var i) es) xs) = Just $ intApp (intSub es i) xs
  where
  intApp : Tm n -> List (Tm n) -> Tm n
  intApp e []      = e
  intApp e (x::xs) = intApp (App e x) xs
from _                             = Nothing

step : Krivine m -> Maybe (Krivine m)
step (MkKAM (MkExp (Var i)             as)     xs ) = Just $ MkKAM (MkExp (intSub as i) I) xs
step (MkKAM (MkExp (Lam _)             _ )     [] ) = Nothing
step (MkKAM (MkExp (Lam e)             as) (x::xs)) = Just $ MkKAM (MkExp e (x::as)) xs
step (MkKAM (MkExp (App e0 e1)         as)     xs ) = Just $ MkKAM (MkExp e0 as) (Esb (MkExp e1 as) :: xs)
step (MkKAM (MkExp (Esb (MkExp et es)) as)     xs ) = Just $ MkKAM (MkExp et (Ss as es)) xs

iter : Krivine m -> Maybe (Krivine m)
iter st@(MkKAM (MkExp (Var i) as) _) = case intSub as i of 
  Var n => Just st
  _ => assert_total $ step st >>= iter
iter st@(MkKAM (MkExp (Lam _) _) []) = Just st
iter st@_ = assert_total $ step st >>= iter

whnf : Tm m -> Maybe (Tm m)
whnf e = iter (into e) >>= from

run : Tm m -> Maybe (Tm m)
run = map resolve . whnf 

-- Church

ff : Clo
ff = Lam $ Lam $ Var FZ

tt : Clo
tt = Lam $ Lam $ Var $ FS FZ

not : Clo
not = Lam $ App (App (Var FZ) (Esb (MkExp ff []))) (Esb (MkExp tt []))

and : Clo
and = Lam $ Lam $ App (App (Var $ FS FZ) (Var FZ)) (Var $ FS FZ)

or : Clo
or = Lam $ Lam $ App (App (Var $ FS FZ) (Var $ FS FZ)) (Var FZ) 

xor : Clo
xor = Lam $ Lam $ App (App (Var $ FS FZ) $ App (Esb (MkExp not [])) (Var FZ)) (Var FZ) 

eq : Clo
eq = Lam $ Lam $ App (Esb (MkExp not [])) $ App (App (Esb (MkExp xor [])) (Var $ FS FZ)) (Var FZ) 

ifc : Clo
ifc = Lam $ Lam $ Lam $ App (App (Var $ FS $ FS FZ) (Var $ FS FZ)) (Var FZ) 

ex0 : Clo
ex0 = App (App and tt) ff

ex1 : Clo
ex1 = App (App or tt) ff

ex2 : Clo
ex2 = App (App eq tt) tt

ex3 : Clo
ex3 = App (App eq tt) ff

omega : Clo
omega = App (Lam $ App (Var FZ) (Var FZ)) (Lam $ App (Var FZ) (Var FZ))

ex3Red0 : Clo
ex3Red0 = Esb $ MkExp ff $ 
                      Ss (Ss Defun.I ( (Esb (MkExp (App (App (Esb (MkExp xor [])) (Var $ FS FZ)) (Var FZ)) 
                                                   ((Esb (MkExp ff I)) :: (Esb (MkExp tt I)) :: I) 
                                       )) :: 
                                       (Ss ((Esb (MkExp Defun.ff I)) :: (Esb (MkExp tt I)) :: I) [])
                                     )
                         ) []

ex3Eq0 : whnf Defun.ex3 = Just Defun.ex3Red0
ex3Eq0 = Refl

ex3Eq1 : run Defun.ex3 = Just Defun.ff
ex3Eq1 = Refl
