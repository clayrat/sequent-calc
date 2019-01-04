module ES.Defun

import Data.Fin

%access public export
%default total

data Ren : Nat -> Nat -> Type where
  Up : Ren m (S m)
  Rw : Ren m n -> Ren (S m) (S n)

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

V0 : Tm (S n)
V0 = Var FZ

V1 : Tm (2+n)
V1 = Var $ FS FZ

V2 : Tm (3+n)
V2 = Var $ FS $ FS FZ

V3 : Tm (4+n)
V3 = Var $ FS $ FS $ FS FZ

V4 : Tm (5+n)
V4 = Var $ FS $ FS $ FS $ FS FZ

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
  intSub (e::_)    FZ    = e
  intSub (_::t)   (FS i) = intSub t i
  intSub []        i     = absurd i
  intSub  I        i     = Var i
  intSub (Sw _)    FZ    = V0
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
ff = Lam $ Lam V0

tt : Clo
tt = Lam $ Lam V1

not : Clo
not = Lam $ App (App V0 (Esb $ MkExp ff [])) (Esb $ MkExp tt [])

and : Clo
and = Lam $ Lam $ App (App V1 V0) V1

or : Clo
or = Lam $ Lam $ App (App V1 V1) V0 

xor : Clo
xor = Lam $ Lam $ App (App V1 $ App (Esb $ MkExp not []) V0) V0 

eq : Clo
eq = Lam $ Lam $ App (Esb $ MkExp not []) $ App (App (Esb $ MkExp xor []) V1) V0

ifc : Clo
ifc = Lam $ Lam $ Lam $ App (App V2 V1) V0

ex0 : Clo
ex0 = App (App and tt) ff

ex1 : Clo
ex1 = App (App or tt) ff

ex2 : Clo
ex2 = App (App eq tt) tt

ex3 : Clo
ex3 = App (App eq tt) ff

omega : Clo
omega = App (Lam $ App V0 V0) (Lam $ App V0 V0)

ex3Red0 : Clo
ex3Red0 = Esb $ MkExp ff $ 
                      Ss (Ss I ( (Esb (MkExp (App (App (Esb $ MkExp xor []) V1) V0) 
                                             ((Esb $ MkExp ff I) :: (Esb $ MkExp tt I) :: I) 
                                 )) :: 
                                 (Ss ((Esb $ MkExp ff I) :: (Esb $ MkExp tt I) :: I) [])
                               )
                         ) []

ex3Eq0 : whnf Defun.ex3 = Just Defun.ex3Red0
ex3Eq0 = Refl

ex3Eq1 : run Defun.ex3 = Just Defun.ff
ex3Eq1 = Refl

-- Cooked

false : Clo
false = Lam $ Lam V1

true : Clo
true = Lam $ Lam V0

if2 : Clo
if2 = Lam $ Lam $ Lam $ App (App V2 V0) V1

zero : Clo
zero = Lam $ Lam V1

succ : Clo
succ = Lam $ Lam $ Lam $ App V0 V2

one : Clo 
one = App succ zero

two : Clo 
two = App succ one

three : Clo
three = App succ two

isZero : Clo
isZero = Lam $ App (App V0 (Esb $ MkExp true [])) (Lam $ Esb $ MkExp false [])

const : Clo
const = Lam $ Lam $ V1

pair : Clo
pair = Lam $ Lam $ Lam $ App (App V0 V2) V1

fstc : Clo
fstc = Lam $ App V0 (Lam $ Lam V1)

sndc : Clo
sndc = Lam $ App V0 (Lam $ Lam V0)

fix : Clo
fix = Lam $ App (Lam $ App V1 $ App V0 V0) (Lam $ App V1 $ App V0 V0)

add : Clo
add = App fix $ Lam $ Lam $ Lam $ App (App V1 V0) (Lam $ App (Esb $ MkExp succ []) (App (App V3 V0) V1))

mul : Clo
mul = App fix $ Lam $ Lam $ Lam $ App (App V1 (Esb $ MkExp zero [])) (Lam $ App (App (Esb $ MkExp add []) V1) (App (App V3 V0) V1))

fac : Clo
fac = App fix $ Lam $ Lam $ App (App V0 (Esb $ MkExp one [])) (Lam $ App (App (Esb $ MkExp mul []) V1) (App V2 V0))

eqnat : Clo
eqnat = App fix $ 
            Lam $ Lam $ Lam $ App (App V1 
                                       (App (App V0 (Esb $ MkExp true [])) (Esb $ MkExp (App const false) []))) 
                                  (Lam $ App (App V1 (Esb $ MkExp false [])) (Lam $ App (App V4 V1) V0))

sumto : Clo
sumto = App fix $ Lam $ Lam $ App (App V0 (Esb $ MkExp zero [])) (Lam $ App (App (Esb $ MkExp add []) V1) (App V2 V0))

n5 : Clo
n5 = App (App add two) three

n6 : Clo
n6 = App (App add three) three

test : Clo
test = App (App eqnat n5) n6

testEq : run Defun.test = Just Defun.false
testEq = Refl

{-
-- takes too long

n17 : Clo
n17 = App (App add n6) (App (App add n6) n5)

n37 : Clo
n37 = App succ (App (App mul n6) n6)

n703 : Clo
n703 = App sumto n37

n720 : Clo
n720 = App fac n6

test : Clo
test = App (App eqnat (App (App mul three) n6)) (App (App add one) n17)
-}