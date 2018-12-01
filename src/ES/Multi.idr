module ES.Multi

import Data.Fin

%access public export
%default total

Shape : Type
Shape = Nat

data BVar : Shape -> Shape -> Type where
  BZ : BVar m (S n)
  BS : BVar m n -> BVar m (S n)

data Tel : (Shape -> Shape -> Type) -> Shape -> Shape -> Shape -> Type where
  NT : Tel b s t t
  CT : Tel b s t u -> b s u -> Tel b s t (S u)

data Vec : Type -> Shape -> Shape -> Type where
  NV  : Vec a r r
  CV : a -> Vec a s t -> Vec a s (S t)

data Ren : Shape -> Shape -> Shape -> Shape -> Type where
  Up : Ren s (S t) s t
  Rw : Ren s t u v -> Ren s (S t) u (S v)

mutual
  data Ob : Shape -> Shape -> Type where
    St  : Ob s t
    Var : BVar s t -> Ob s t
    Pi  : Tel Ob s t u -> Ob s u -> Ob s t
    Lam : LTE t u -> Ob s u -> Ob s t
    App : Vec (Ob s t) s u -> Ob s t -> Ob s t
    Esb : Exp s t -> Ob s t

  record Exp (s : Shape) (t : Shape) where
    constructor MkExp
    u  : Shape
    {v  : Shape}
    ctx : Sub s t u v
    obj : Ob u v

  data Sub : Shape -> Shape -> Shape -> Shape -> Type where
    Rs   : Ren s t u v -> Sub u v w x -> Sub s t w x
    Ss   : Sub s t u v -> Sub u v w x -> Sub s t w x
    (::) : Ob s t -> Sub s t u v -> Sub s t u (S t)
    Nil  : Sub s t r r
    I    : Sub s t s t
    Sw   : Sub s t u v -> Sub s (S t) u (S v)

wk : (r : Shape) -> Ob r r -> Ob s t
wk r e = Esb $ MkExp r [] e

Clo : Type
Clo = {r : Shape} -> Ob r r

pi : Clo
pi = Pi (((NT `CT` St) `CT` Var BZ) `CT` Var (BS BZ)) St