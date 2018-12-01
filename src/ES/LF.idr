module ES.LF

import Data.Fin

%access public export
%default total

Shape : Type
Shape = Nat

BVar : Shape -> Type
BVar = Fin

FVar : Type
FVar = String

data Ren : Shape -> Shape -> Type where
  Up : Ren (S s) s
  Rw : Ren s t -> Ren (S s) (S t)

mutual
  data Ob : Shape -> Type where
    Var : BVar s -> Ob s
    Pi  : Ob s -> Ob (S s) -> Ob s
    Lam : Ob (S s) -> Ob s
    App : Ob s -> Ob s -> Ob s
    Esb : Exp s -> Ob s

  record Exp (s : Shape) where
    constructor MkExp
    {t  : Shape}
    ctx : Sub s t
    obj : Ob t

  data Sub : Shape -> Shape -> Type where
    Rs   : Ren s t -> Sub t r -> Sub s r
    Ss   : Sub s t -> Sub t r -> Sub s r
    (::) : Ob s -> Sub s t -> Sub s (S t)
    Nil  : Sub s 0
    I    : Sub s s
    Sw   : Sub s t -> Sub (S s) (S t)

V0 : Ob (S n)
V0 = Var FZ

V1 : Ob (2+n)
V1 = Var $ FS FZ

V2 : Ob (3+n)
V2 = Var $ FS $ FS FZ

V3 : Ob (4+n)
V3 = Var $ FS $ FS $ FS FZ

V4 : Ob (5+n)
V4 = Var $ FS $ FS $ FS $ FS FZ

wk : Ob 0 -> Ob s
wk e = Esb $ MkExp [] e

Env : (Shape -> Type) -> (Shape -> Shape -> Type)
Env f s t = Fin t -> f s

Hom : Shape -> Shape -> Type
Hom s t = Ob t -> Ob s

shift : Ren s t -> Env BVar s t
shift  Up     i     = FS i
shift (Rw p)  FZ    = FZ
shift (Rw p) (FS i) = FS (shift p i)

mutual
  index : Sub s t -> Env Ob s t
  index I         i     = Var i
  index (Rs p r)  i     = ren p (index r i)
  index (Ss s r)  i     = assert_total $ sub s (index r i)
  index (e::_)    FZ    = e
  index (_::r)   (FS i) = index r i
  index []        i     = absurd i
  index (Sw _)    FZ    = Var FZ
  index (Sw s)   (FS i) = ren Up (index s i)

  ren : Ren s t -> Hom s t
  ren p (Var i)           = Var $ shift p i
  ren p (Pi e0 e1)        = Pi (ren p e0) (ren (Rw p) e1)
  ren p (Lam e)           = Lam $ ren (Rw p) e
  ren p (App e0 e1)       = App (ren p e0) (ren p e1)
  ren p (Esb (MkExp r e)) = Esb $ MkExp (Rs p r) e

  sub : Sub s t -> Hom s t
  sub s (Var i)           = index s i
  sub s (Pi e0 e1)        = Pi (sub s e0) (sub (Sw s) e1)
  sub s (Lam e)           = Lam $ sub (Sw s) e
  sub s (App e0 e1)       = App (sub s e0) (sub s e1)
  sub s (Esb (MkExp r e)) = Esb $ MkExp (Ss s r) e

res : Ob s -> Ob s
res (Var i)           = Var i
res (Pi e0 e1)        = Pi (res e0) (res e1)
res (Lam e)           = Lam (res e)
res (App e0 e1)       = App (res e0) (res e1)
res (Esb (MkExp r e)) = assert_total $ res (sub r e)

Stack : Shape -> Type
Stack s = List (Ob s)

record Machine (s : Shape) where
  constructor MkMach
  candidate : Exp s
  stack : Stack s

reflect : Ob s -> Machine s
reflect e = MkMach (MkExp I e) []

from : Machine s -> Ob s
from (MkMach (MkExp r (Lam e)) []) = Esb $ MkExp r (Lam e)
from (MkMach (MkExp r (Var i)) xs) = go (index r i) xs
  where
  go : Ob n -> Stack n -> Ob n
  go e [] = e
  go f (x::xs) = go (App f x) xs
from s = assert_total $ from s   -- diverge

step : Machine s -> Machine s
step (MkMach (MkExp r (Lam e))         (x::xs)) = MkMach (MkExp (x::r) e)                          xs
step (MkMach (MkExp r (App e0 e1))         xs ) = MkMach (MkExp r e0)         ((Esb $ MkExp r e1)::xs)
step (MkMach (MkExp r (Esb (MkExp s e)))   xs ) = MkMach (MkExp (Ss r s) e)                        xs
step (MkMach (MkExp r (Var i))             xs ) = MkMach (MkExp I (index r i))                     xs -- shouldn't occur with iter
step s = assert_total $ step s -- diverge 

canon : Ob s -> Bool
canon (Pi _ _) = True
canon (Lam _)  = True
canon _        = False

iter : Machine s -> Machine s
iter i@(MkMach (MkExp r e)     []) = if canon e then i else assert_total $ iter (step i)
iter   (MkMach (MkExp r (Var i)) xs) with (index r i)
  | Var j = MkMach (MkExp I (Var j)) xs
  | e = assert_total $ iter $ MkMach (MkExp I e) xs
iter i = assert_total $ iter (step i)

reify : Machine s -> Ob s
reify g = res (from (iter g))

whnf : Ob s -> Ob s
whnf e = reify (reflect e)

-- Cooked

false : Ob Z
false = Lam $ Lam $ V1

true : Ob Z
true = Lam $ Lam $ V0

if2 : Ob Z
if2 = Lam $ Lam $ Lam $ App (App V2 V0) V1

zero : Ob Z
zero = Lam $ Lam $ V1

succ : Ob Z
succ = Lam $ Lam $ Lam $ App V0 V2

one : Ob Z 
one = App succ zero

two : Ob Z 
two = App succ one

three : Ob Z
three = App succ two

const : Ob Z
const = Lam $ Lam $ V1

fix : Ob Z
fix = Lam $ App (Lam $ App V1 $ App V0 V0) (Lam $ App V1 $ App V0 V0)

add : Ob Z
add = App fix $ Lam $ Lam $ Lam $ App (App V1 V0) (Lam $ App (wk succ) (App (App V3 V0) V1))

mul : Ob Z
mul = App fix $ Lam $ Lam $ Lam $ App (App V1 (wk zero)) (Lam $ App (App (wk add) V1) (App (App V3 V0) V1))

eqnat : Ob Z
eqnat = App fix $ 
            Lam $ Lam $ Lam $ App (App V1 
                                       (App (App V0 (wk true)) (wk (App const false)))) 
                                  (Lam $ App (App V1 (wk false)) (Lam $ App (App V4 V1) V0))

n5 : Ob Z
n5 = App (App add two) three

n6 : Ob Z
n6 = App (App add three) three

n17 : Ob Z
n17 = App (App add n6) (App (App add n6) n5)

n37 : Ob Z
n37 = App succ (App (App mul n6) n6)

test : Ob Z
test = App (App eqnat (App (App mul three) n6)) (App (App add one) n17)
