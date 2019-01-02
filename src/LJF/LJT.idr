module LJF.LJT

import Data.List
import Subset

%default total
%access public export

data Ty = A | Imp Ty Ty
infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp

mutual
  data Async : List Ty -> Ty -> Type where
    Foc : Elem a g -> LSync g a b -> Async g b
    IR  : Async (a::g) b -> Async g (a~>b)
    HC  : Async g a -> LSync g a b -> Async g b       -- head cut
    MC  : Async g a -> Async (a::g) b -> Async g b    -- mid cut
  
  data LSync : List Ty -> Ty -> Ty -> Type where
    Ax  : LSync g a a 
    IL  : Async g a -> LSync g b c -> LSync g (a~>b) c
    FHC : LSync g b a -> LSync g a c -> LSync g b c     -- focused head cut, concatenating contexts
    FMC : Async g a -> LSync (a::g) b c -> LSync g b c  -- focused mid cut

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

reduceA : Async g a -> Maybe (Async g a)
reduceA (HC (IR t)     (IL u k)          ) = Just $ HC (MC u t) k
reduceA (HC (Foc el k)  m                ) = Just $ Foc el (FHC k m)
reduceA (MC  u         (IR t)            ) = Just $ IR $ MC (shiftAsync {is=ConsR Id} u) (shiftAsync t) 
reduceA (MC  u         (Foc  Here      k)) = Just $ HC u (FMC u k)
reduceA (MC  u         (Foc (There el) k)) = Just $ Foc el (FMC u k)
reduceA  _                                = Nothing

reduceLS : LSync g a b -> Maybe (LSync g a b)
reduceLS (FHC  Ax       m      ) = Just m
reduceLS (FHC (IL u k)  m      ) = Just $ IL u (FHC k m)
reduceLS (FMC  _        Ax     ) = Just Ax
reduceLS (FMC  u       (IL t k)) = Just $ IL (MC u t) (FMC u k)
reduceLS  _                      = Nothing
