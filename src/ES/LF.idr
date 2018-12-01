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
