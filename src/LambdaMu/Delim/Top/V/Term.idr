module LambdaMu.Delim.Top.V.Term

import Data.List

%default total

data Ty = INT | STR | BOOL | Imp Ty Ty Ty Ty

mutual
  data Term : List Ty -> Ty -> Ty -> List (Ty, Ty) -> Ty -> Type where
    V     : Val g t a d s -> Term g t a d s
    App   : Term g u1 (Imp a t1 u2 b) d t2 -> Term g t1 a d u1 -> Term g u2 b d t2
    Mu    : Cmd g ((a,u)::d) t -> Term g u a d t
    MuTop : Cmd g d a -> Term g t a d t
    Eq    : Term g t1 a d t -> Term g u a d t1 -> Term g u BOOL d t

  data Val : List Ty -> Ty -> Ty -> List (Ty, Ty) -> Ty -> Type where
    Var : Elem a g -> Val g t a d t
    I   : Integer -> Val g u INT d t
    S   : String -> Val g u STR d t
    Su  : Term g u INT d t -> Val g u INT d t
    Lam : Term (a::g) u b d t -> Val g s (Imp a t u b) d s

  data Cmd : List Ty -> List (Ty, Ty) -> Ty -> Type where
    Named : Elem (a,u) d -> Term g u a d t -> Cmd g d t
    Top   : Term g u u d t -> Cmd g d t

abort : Term g v v ((a,u)::d) t -> Term g u a d t
abort m = Mu $ Top m

ex12 : Term g t BOOL d t
ex12 = MuTop $ Top $ V $ Su $ Mu $ Top $ Eq (V $ I 2)
                                            (MuTop $ Named Here (V $ I 3))

ex13 : Term g t INT d t
ex13 = MuTop $ Top $ Eq {t1=STR} {a=BOOL} (abort $ V $ I 5) (abort $ V $ S "Hello") -- `a` in Eq can be anything