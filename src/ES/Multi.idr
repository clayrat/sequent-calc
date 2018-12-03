module ES.Multi

import Data.Fin

%access public export
%default total

Shape : Type
Shape = Nat

data BVar : Shape -> Shape -> Type where
  BZ : BVar m (S n)
  BS : BVar m n -> BVar m (S n)

data LTEr : Shape -> Shape -> Type where
  LR : LTEr m m
  LS : LTEr m n -> LTEr m (S n)

data Tel : (Shape -> Shape -> Type) -> Shape -> Shape -> Shape -> Type where
  NT : Tel b s t t
  CT : Tel b s t u -> b s u -> Tel b s t (S u)

data Vec : Type -> Shape -> Shape -> Type where
  Nil  : Vec a r r
  (::) : a -> Vec a s t -> Vec a s (S t)

data Ren : Shape -> Shape -> Shape -> Shape -> Type where
  Up : Ren s (S t) s t
  Rw : Ren s t u v -> Ren s (S t) u (S v)

mutual
  data Ob : Shape -> Shape -> Type where
    St  : Ob s t
    Var : BVar s t -> Ob s t
    Pi  : Tel Ob s t u -> Ob s u -> Ob s t
    Lam : LTEr t u -> Ob s u -> Ob s t
    App : Vec (Ob s t) s u -> Ob s t -> Ob s t
    Esb : Exp s t -> Ob s t

  record Exp (s : Shape) (t : Shape) where
    constructor MkExp
    u  : Shape
    {v  : Shape}
    ctx : Sub s t u v
    obj : Ob u v

  data Sub : Shape -> Shape -> Shape -> Shape -> Type where
    Rs : Ren s t u v -> Sub u v w x -> Sub s t w x
    Ss : Sub s t u v -> Sub u v w x -> Sub s t w x
    CS : Ob s t -> Sub s t u v -> Sub s t u (S t)
    CN : Sub s t r r
    I  : Sub s t s t
    Sw : Sub s t u v -> Sub s (S t) u (S v)

V0 : Ob m (S n)
V0 = Var BZ    

V1 : Ob m (2+n)
V1 = Var $ BS BZ

V2 : Ob m (3+n)
V2 = Var $ BS $ BS BZ

V3 : Ob m (4+n)
V3 = Var $ BS $ BS $ BS BZ

wk : (r : Shape) -> Ob r r -> Ob s t
wk r e = Esb $ MkExp r CN e

Clo : Type
Clo = {r : Shape} -> Ob r r

pi : Clo
pi = Pi (((NT `CT` St) `CT` V0) `CT` V1) St

app : Ob s t -> Ob s t -> Ob s t
app a b = App [a] b

-- Cooked

false : Clo
false = Lam (LS $ LS LR) V1

true : Clo
true = Lam (LS $ LS LR) V0

zero : Clo
zero = Lam (LS $ LS LR) V1

succ : Clo
succ = Lam (LS $ LS $ LS $ LR) $ app V0 V2

one : Clo
one = app succ zero

two : Clo
two = app succ one

three : Clo
three = app succ two

const : Clo
const = Lam (LS $ LS LR) V1

fix : Clo
fix = Lam (LS LR) $ 
      app (Lam (LS LR) $ app V1 (app V0 V0))
          (Lam (LS LR) $ app V1 (app V0 V0))
add : Clo
add {r} = app fix $ 
          Lam (LS $ LS $ LS LR) $ 
              App [V1, V0] $ 
                  Lam (LS LR) $ 
                      app (wk r succ) $ 
                          App [V3, V0] V1

mul : Clo
mul {r} = app fix $ 
          Lam (LS $ LS $ LS LR) $ 
              App [V1, wk r zero] $ 
                  Lam (LS LR) $ 
                      App [wk r add, V1] $
                          App [V3, V0] V1
