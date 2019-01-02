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

mutual
  data Async : List PTy -> NTy -> Type where
    FL  : Elem (D n) g -> LSync g n m -> Async g m
    FR  : RSync g p -> Async g (U p)
    IR  : Async (p::g) n -> Async g (p~>n)
    HCL : Async g n -> LSync g n m -> Async g m     -- left head cut
    HCR : RSync g p -> Async (p::g) n -> Async g n  -- right head cut
  
  data LSync : List PTy -> NTy -> NTy -> Type where
    AxL  : Not (n=Imp p m) -> LSync g n n 
    BL   : Async (p::g) m -> LSync g (U p) m 
    IL   : RSync g p -> LSync g n m -> LSync g (p~>n) m
    FCL  : LSync g m n -> LSync g n l -> LSync g m l     -- focused left cut, concatenating contexts
    FCRM : RSync g p -> LSync (p::g) n m -> LSync g n m  -- focused right cut minus

  data RSync : List PTy -> PTy -> Type where
    AxR  : Elem p g -> RSync g p
    BR   : Async g n -> RSync g (D n)
    FCRP : RSync g p -> RSync (p::g) q -> RSync g q    -- focused right cut plus