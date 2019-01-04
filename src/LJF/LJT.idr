module LJF.LJT

import Data.List
import Subset
import Lambda.Ty
import Lambda.Lam

%default total
%access public export

mutual
  data Async : List Ty -> Ty -> Type where
    Foc : Elem a g -> LSync g a b -> Async g b      -- ~contraction
    IR  : Async (a::g) b -> Async g (a~>b)          -- lambda  
    HC  : Async g a -> LSync g a b -> Async g b     -- head cut, beta-redex
    MC  : Async g a -> Async (a::g) b -> Async g b  -- mid cut, term explicit substitution
  
  data LSync : List Ty -> Ty -> Ty -> Type where
    Ax  : LSync g a a                                   -- empty list
    IL  : Async g a -> LSync g b c -> LSync g (a~>b) c  -- prepending argument
    FHC : LSync g b a -> LSync g a c -> LSync g b c     -- focused head cut, concatenating contexts
    FMC : Async g a -> LSync (a::g) b c -> LSync g b c  -- focused mid cut, list explicit substitution

-- TODO for some reason totality checking takes a few minutes here without asserts
mutual 
  shiftAsync : {auto is : IsSubset g g1} -> Async g a -> Async g1 a
  shiftAsync {is} (Foc el k) = Foc (shift is el) (assert_total $ shiftLSync k)
  shiftAsync {is} (IR t)     = IR (assert_total $ shiftAsync {is=Cons2 is} t)
  shiftAsync      (HC t c)   = HC (assert_total $ shiftAsync t) (assert_total $ shiftLSync c)
  shiftAsync {is} (MC t t2)  = MC (assert_total $ shiftAsync t) (assert_total $ shiftAsync {is=Cons2 is} t2)
  
  shiftLSync : {auto is : IsSubset g g1} -> LSync g a b -> LSync g1 a b
  shiftLSync       Ax        = Ax
  shiftLSync      (IL t c)   = IL  (assert_total $ shiftAsync t) (assert_total $ shiftLSync c)
  shiftLSync      (FHC c c2) = FHC (assert_total $ shiftLSync c) (assert_total $ shiftLSync c2)
  shiftLSync {is} (FMC t c)  = FMC (assert_total $ shiftAsync t) (assert_total $ shiftLSync {is=Cons2 is} c)

-- reductions (TODO useless because redexes are buried)

reduceA : Async g a -> Maybe (Async g a)
reduceA (HC (IR t)     (IL u k)          ) = Just $ HC (MC u t) k
--reduceA (HC (IR t)      Ax               ) = Just $ IR t
reduceA (HC (Foc el k)  m                ) = Just $ Foc el (FHC k m)
--reduceA (HC (HC t k)    m                ) = Just $ HC t (FHC k m)
reduceA (MC  u         (IR t)            ) = Just $ IR $ MC (shiftAsync u) (shiftAsync t) 
reduceA (MC  u         (Foc  Here      k)) = Just $ HC u (FMC u k)
reduceA (MC  u         (Foc (There el) k)) = Just $ Foc el (FMC u k)
reduceA  _                                 = Nothing

reduceLS : LSync g a b -> Maybe (LSync g a b)
reduceLS (FHC  Ax       m      ) = Just m
reduceLS (FHC (IL u k)  m      ) = Just $ IL u (FHC k m)
reduceLS (FMC  _        Ax     ) = Just Ax
reduceLS (FMC  u       (IL t k)) = Just $ IL (MC u t) (FMC u k)
-- p to x.(t k) → (p to x.t)(p to x.k) ?
reduceLS  _                      = Nothing

-- STLC embedding

encode : Tm g a -> Async g a   
encode (Vr e)    = Foc e Ax
encode (Lm t)    = IR $ encode t
encode (Ap t t2) = HC (encode t) (IL (encode t2) Ax)

-- TJAM

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : Async g a -> Env g -> Clos a

lookup : Elem a g -> Env g -> Clos a    
lookup  Here      (c::_) = c
lookup (There el) (_::e) = lookup el e

data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Clos a -> Stack b c -> Stack (a~>b) c

snoc : Stack a (b~>c) -> Clos b -> Stack a c
snoc  NS        c = CS c NS
snoc (CS c1 st) c = CS c1 (snoc st c)

append : Stack a b -> Stack b c -> Stack a c
append  NS       s2 = s2
append (CS c s1) s2 = CS c (append s1 s2)

data State : Ty -> Type where
  S1 : Async g a -> Env g -> Stack a b -> State b
  S2 : Async g a -> Env g -> Stack a x -> LSync d x y -> Env d -> Stack y b -> State b

initState : Async [] a -> State a
initState a = S1 a [] NS

step : State b -> Maybe (State b)
step (S1 (IR t    ) en (CS ug c)) = Just $ S1 t (ug::en) c
step (S1 (Foc el k) en        c ) = let Cl t g = lookup el en in 
                                    Just $ S2 t g NS k en c
step (S1 (HC t   k) en        c ) = Just $ S2 t en NS k en c
step (S2 t en b  Ax      g c) = Just $ S1 t en (append b c)
step (S2 t en b (IL u k) g c) = Just $ S2 t en (snoc b (Cl u g)) k g c
step _ = Nothing
