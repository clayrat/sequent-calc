module LJF.LJQ

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
    Foc : RSync g a -> Async g a
    IL  : RSync g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c  -- generalized application
    HC  : RSync g a -> Async (a::g) b -> Async g b                   -- head cut
    MC  : Async g a -> Async (a::g) b -> Async g b                   -- mid cut

  data RSync : List Ty -> Ty -> Type where
    Ax  : Elem a g -> RSync g a 
    IR  : Async (a::g) b -> RSync g (a~>b)
    FHC : RSync g a -> RSync (a::g) b -> RSync g b -- focused head cut
    -- no focused mid cut    

mutual 
  shiftAsync : {auto is : IsSubset g g1} -> Async g a -> Async g1 a
  shiftAsync      (Foc r)     = Foc $ shiftRSync r
  shiftAsync {is} (IL r a el) = IL (shiftRSync r) (shiftAsync {is=Cons2 is} a) (shift is el)
  shiftAsync {is} (HC r a)    = HC (shiftRSync r) (shiftAsync {is=Cons2 is} a)
  shiftAsync {is} (MC r l)    = MC (shiftAsync r) (shiftAsync {is=Cons2 is} l)
  
  shiftRSync : {auto is : IsSubset g g1} -> RSync g a -> RSync g1 a
  shiftRSync {is} (Ax el)   = Ax $ shift is el
  shiftRSync {is} (IR a)    = IR (shiftAsync {is=Cons2 is} a)
  shiftRSync {is} (FHC r l) = FHC (shiftRSync r) (shiftRSync {is=Cons2 is} l)

reduceA : Async g a -> Maybe (Async g a)
reduceA (HC   (Ax el    )  t                 ) = Just $ shiftAsync {is=ctr el} t
reduceA (HC a@(IR _     ) (Foc p            )) = Just $ Foc $ FHC a p
reduceA (HC a@(IR u     ) (IL p t  Here     )) = Just $ MC (HC (FHC a p) u) (HC (shiftRSync a) (shiftAsync t)) 
reduceA (HC a@(IR _     ) (IL p t (There el))) = Just $ IL (FHC a p) (HC (shiftRSync a) (shiftAsync t)) el
reduceA (MC   (Foc p    )  t                 ) = Just $ HC p t
reduceA (MC   (IL p v el)  t                 ) = Just $ IL p (MC v (shiftAsync t)) el
reduceA  _                                     = Nothing

reduceR : RSync g a -> Maybe (RSync g a)
reduceR (FHC   (Ax el)  p             ) = Just $ shiftRSync {is=ctr el} p
reduceR (FHC a@(IR _)  (Ax  Here     )) = Just a
reduceR (FHC   (IR _)  (Ax (There el))) = Just $ Ax el
reduceR (FHC a@(IR _)  (IR t         )) = Just $ IR $ HC (shiftRSync a) (shiftAsync t)
reduceR  _                              = Nothing
