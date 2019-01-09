module LJF.LJF

import Data.List
import Subset

%default total
%access public export

mutual
  data PTy = AP | D NTy 
  
  data NTy = AM | U PTy | Imp PTy NTy 

infix 5 ~>
(~>) : PTy -> NTy -> NTy
(~>) = Imp

-- unary negative formula
data UN : NTy -> Type where
  UA : UN  AM
  UU : UN (U p)

mutual
  data Async : List PTy -> NTy -> Type where
    FL  : Elem (D n) g -> LSync g n m -> Async g m  -- left focus
    FR  : RSync g p -> Async g (U p)                -- right focus
    IR  : Async (p::g) n -> Async g (p~>n)          -- lambda
    HCL : Async g n -> LSync g n m -> Async g m     -- left head cut
    HCR : RSync g p -> Async (p::g) n -> Async g n  -- right head cut
  
  data LSync : List PTy -> NTy -> NTy -> Type where
    AxL  : UN n -> LSync g n n                
    BL   : Async (p::g) m -> LSync g (U p) m             -- left blur
    IL   : RSync g p -> LSync g n m -> LSync g (p~>n) m
    FCL  : LSync g m n -> LSync g n l -> LSync g m l     -- focused left cut, concatenating contexts
    FCRN : RSync g p -> LSync (p::g) n m -> LSync g n m  -- focused right negative cut

  data RSync : List PTy -> PTy -> Type where
    AxR  : Elem p g -> RSync g p
    BR   : Async g n -> RSync g (D n)                -- right blur
    FCRP : RSync g p -> RSync (p::g) q -> RSync g q  -- focused right positive cut

mutual 
  shiftAsync : {auto is : IsSubset g g1} -> Async g a -> Async g1 a
  shiftAsync {is} (FL el k) = FL (shift is el) (shiftLSync k)
  shiftAsync      (FR r)    = FR $ shiftRSync r
  shiftAsync {is} (IR t)    = IR (shiftAsync {is=Cons2 is} t)
  shiftAsync      (HCL t c) = HCL (shiftAsync t) (shiftLSync c)
  shiftAsync {is} (HCR r a)  = HCR (shiftRSync r) (shiftAsync {is=Cons2 is} a)
  
  shiftLSync : {auto is : IsSubset g g1} -> LSync g a b -> LSync g1 a b
  shiftLSync      (AxL prf)  = AxL ?wat0
  shiftLSync      (BL a)     = BL ?wat
  shiftLSync      (IL t c)   = IL  (shiftRSync t) (shiftLSync c)
  shiftLSync      (FCL c c2) = FCL (shiftLSync c) (shiftLSync c2)
  shiftLSync {is} (FCRN t c) = FCRN (shiftRSync t) (shiftLSync {is=Cons2 is} c)

  shiftRSync : {auto is : IsSubset g g1} -> RSync g a -> RSync g1 a
  shiftRSync {is} (AxR el)   = AxR $ shift is el
  shiftRSync {is} (BR a)     = BR ?wat2
  shiftRSync {is} (FCRP r l) = FCRP (shiftRSync r) (shiftRSync {is=Cons2 is} l)

