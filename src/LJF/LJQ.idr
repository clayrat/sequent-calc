module LJF.LJQ

import Data.List
import Subset
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

mutual
  data Async : List Ty -> Ty -> Type where
    Foc : RSync g a -> Async g a                                     
    IL  : RSync g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c  -- generalized application
    HC  : RSync g a -> Async (a::g) b -> Async g b                   -- head cut, explicit substution
    MC  : Async g a -> Async (a::g) b -> Async g b                   -- mid cut, beta-redex

  data RSync : List Ty -> Ty -> Type where
    Ax  : Elem a g -> RSync g a 
    IR  : Async (a::g) b -> RSync g (a~>b)          -- lambda
    FHC : RSync g a -> RSync (a::g) b -> RSync g b  -- focused head cut
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

-- STLC embedding

-- Moggi's lambda-C
mutual
  data Val : List Ty -> Ty -> Type where
    Var : Elem a g -> Val g a 
    Lam : Tm (a::g) b -> Val g (a~>b)

  data Tm : List Ty -> Ty -> Type where
    V   : Val g a -> Tm g a
    App : Tm g (a~>b) -> Tm g a -> Tm g b
    Let : Tm g a -> Tm (a::g) b -> Tm g b  

mutual 
  shiftVal : {auto is : IsSubset g g1} -> Val g a -> Val g1 a
  shiftVal {is} (Var el) = Var $ shift is el
  shiftVal {is} (Lam t)  = Lam $ shiftTm {is=Cons2 is} t
  
  shiftTm : {auto is : IsSubset g g1} -> Tm g a -> Tm g1 a
  shiftTm      (V v)       = V $ shiftVal v
  shiftTm      (App t1 t2) = App (shiftTm t1) (shiftTm t2)
  shiftTm {is} (Let m n)   = Let (shiftTm m) (shiftTm {is=Cons2 is} n)
    
embedLC : Term g a -> Tm g a
embedLC (Var e)     = V $ Var e
embedLC (Lam t)     = V $ Lam $ embedLC t
embedLC (App t1 t2) = App (embedLC t1) (embedLC t2)

mutual  
  encodeVal : Val g a -> RSync g a
  encodeVal (Var e) = Ax e
  encodeVal (Lam t) = IR $ encodeTm t

  encodeTm : Tm g a -> Async g a   
  encodeTm (V    v                        ) = Foc $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p ) = IL (encodeVal v) (encodeTm p) e
  encodeTm (Let (App (V (Lam t)) (V v)) p ) = MC (Foc $ IR $ encodeTm t) (IL (shiftRSync $ encodeVal v) (shiftAsync $ encodeTm p) Here)
  encodeTm (Let (App (V  v     )  n   ) p ) = assert_total $ encodeTm $ Let n $ Let (App (V $ shiftVal v) (V $ Var Here)) (shiftTm p)
  encodeTm (Let (App  m           n   ) p ) = assert_total $ encodeTm $ Let m $ Let (App (V $ Var Here) (shiftTm n)) (shiftTm p)
  encodeTm (Let (Let  m           n   ) p ) = assert_total $ encodeTm $ Let m $ Let n (shiftTm p)
  encodeTm (Let (V    v               ) p ) = MC (Foc $ encodeVal v) (encodeTm p)
  encodeTm (App  t1                     t2) = assert_total $ encodeTm $ Let (App t1 t2) (V $ Var Here)

encode : Term g a -> Async g a
encode = encodeTm . embedLC  

-- QJAM

mutual
  data Env : List Ty -> Type where
    Nil  : Env []
    (::) : Clos a -> Env g -> Env (a::g)
  
  data Clos : Ty -> Type where
    Cl : RSync g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  NS : Stack a a
  CS : Clos a -> Stack b c -> Stack (a~>b) c

data State : Ty -> Type where
  S1 : Async g a -> Env g -> Stack a b -> State b
--  S2 : Async g a -> Env g -> Stack a x -> LSync d x y -> Env d -> Stack y b -> State b  

step : State b -> Maybe (State b)
step (S1 (Foc p)    e (CS tg c)) = ?wat_1
step (S1 (IL p t x) e        c ) = ?wat_2
step (S1 (HC r a)   e        c ) = ?wat_3
step _ = Nothing