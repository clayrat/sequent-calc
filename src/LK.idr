module LK

import Data.List
import Data.Fin

%default total
%access public export

--TODO forall/exists
data Ty = Atom 
        | Top
        | Bot
        | Conj Ty Ty
        | Disj Ty Ty
        | Neg Ty
        | Fn Ty Ty
        | Sub Ty Ty

infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Fn

data Sequent = Ts (List Ty) (List Ty)

infix 4 |-
(|-) : List Ty -> List Ty -> Sequent
(|-) = Ts

data LK : Sequent -> Type where
  Ax     : LK ([a] |- [a])                     
  Cut    : LK (g |- a::d) -> LK (a::s |- p) -> LK (g++s |- d++p)
  TopR   : LK (g |- Top::d)
  BotL   : LK (Bot::g |- d)
  ConjR  : LK (g |- a::d) -> LK (g |- b::d) -> LK (g |- Conj a b :: d)
  ConjL1 : LK (a::g |- d) -> LK (Conj a b :: g |- d)
  ConjL2 : LK (b::g |- d) -> LK (Conj a b :: g |- d)
  DisjR1 : LK (g |- a::d) -> LK (g |- Disj a b :: d)
  DisjR2 : LK (g |- b::d) -> LK (g |- Disj a b :: d)
  DisjL  : LK (a::g |- d) -> LK (b::g |- d) -> LK (Disj a b :: g |- d)
  NegL   : LK (g |- a::d) -> LK (Neg a :: g |- d)
  NegR   : LK (a::g |- d) -> LK (g |- Neg a :: d)
  ImpL   : LK (g |- a::d) -> LK (b::s |- p) -> LK ((a~>b)::g++s |- d++p)
  ImpR   : LK (a::g |- b::d) -> LK (g |- (a~>b)::d)
  SubL   : LK (a::g |- b::d) -> LK (Sub a b ::g |- d)
  SubR   : LK (g |- a::d) -> LK (b::s |- p) -> LK (g++s |- Sub a b :: d++p)
  WL     : LK (g |- d) -> LK (a::g |- d)
  CL     : LK (a::a::g |- d) -> LK (a::g |- d) 
  PL     : LK (g ++ a::b::s |- d) -> LK (g ++ b::a::s |- d) 
  WR     : LK (g |- d) -> LK (g |- a::d)
  CR     : LK (g |- a::a::d) -> LK (g |- a::d) 
  PR     : LK (g |- d ++ a::b::s) -> LK (g |- d ++ b::a::s) 

forwardCtxL : (g, s : List Ty) -> LK ((g++s)++(a::d) |- b) -> LK ((g++a::s)++d |- b)
forwardCtxL g []      {a} {d} lk = 
  rewrite sym $ appendAssociative g [a] d in 
  rewrite sym $ appendNilRightNeutral g in 
  lk
forwardCtxL g (x::xs) {a} {d} lk = 
  rewrite sym $ appendAssociative g (a::x::xs) d in 
  PL {a=x} {b=a} {g} {s=xs++d} $ 
  rewrite appendAssociative g [x] (a::xs ++ d) in 
  rewrite appendAssociative (g++[x]) (a::xs) d in 
  forwardCtxL (g++[x]) xs $ 
  rewrite sym $ appendAssociative g [x] xs in
  lk

forwardCtxR : (g, s : List Ty) -> LK (b |- (g++s)++(a::d)) -> LK (b |- (g++a::s)++d)
forwardCtxR g []      {a} {d} lk = 
  rewrite sym $ appendAssociative g [a] d in 
  rewrite sym $ appendNilRightNeutral g in 
  lk
forwardCtxR g (x::xs) {a} {d} lk = 
  rewrite sym $ appendAssociative g (a::x::xs) d in 
  PR {a=x} {b=a} {d=g} {s=xs++d} $ 
  rewrite appendAssociative g [x] (a::xs ++ d) in 
  rewrite appendAssociative (g++[x]) (a::xs) d in 
  forwardCtxR (g++[x]) xs $ 
  rewrite sym $ appendAssociative g [x] xs in
  lk  

permuteCtxL : (g, s, p : List Ty) -> LK ((g++s)++(p++d) |- a) -> LK ((g++p)++(s++d) |- a)
permuteCtxL g s []      {d} lk = 
  rewrite appendNilRightNeutral g in 
  rewrite appendAssociative g s d in 
  lk
permuteCtxL g s (p::ps) {d} lk = 
  rewrite appendAssociative g [p] ps in 
  permuteCtxL (g++[p]) s ps $
  rewrite sym $ appendAssociative g [p] s in
  forwardCtxL g s {a=p} {d=ps++d} lk

permuteCtxR : (g, s, p : List Ty) -> LK (a |- (g++s)++(p++d)) -> LK (a |- (g++p)++(s++d))
permuteCtxR g s []      {d} lk = 
  rewrite appendNilRightNeutral g in 
  rewrite appendAssociative g s d in 
  lk
permuteCtxR g s (p::ps) {d} lk = 
  rewrite appendAssociative g [p] ps in 
  permuteCtxR (g++[p]) s ps $
  rewrite sym $ appendAssociative g [p] s in
  forwardCtxR g s {a=p} {d=ps++d} lk  

swap3CtxL : (g, s : List Ty) -> LK ((g++s)++p |- a) -> LK ((g++p)++s |- a)
swap3CtxL g s {p} = 
  rewrite sym $ appendNilRightNeutral ((g++s)++p) in
  rewrite sym $ appendNilRightNeutral ((g++p)++s) in
  rewrite sym $ appendAssociative (g++s) p [] in
  rewrite sym $ appendAssociative (g++p) s [] in
  permuteCtxL g s p {d=[]}  

swap3CtxR : (g, s : List Ty) -> LK (a |- (g++s)++p) -> LK (a |- (g++p)++s)
swap3CtxR g s {p} = 
  rewrite sym $ appendNilRightNeutral ((g++s)++p) in
  rewrite sym $ appendNilRightNeutral ((g++p)++s) in
  rewrite sym $ appendAssociative (g++s) p [] in
  rewrite sym $ appendAssociative (g++p) s [] in
  permuteCtxR g s p {d=[]}  

swapCtxL : (s, p : List Ty) -> LK (s++p |- a) -> LK (p++s |- a)  
swapCtxL s p = swap3CtxL [] s

swapCtxR : (s, p : List Ty) -> LK (a |- s++p) -> LK (a |- p++s)  
swapCtxR s p = swap3CtxR [] s

dual : Ty -> Ty
dual Atom       = Atom
dual Top        = Bot
dual Bot        = Top
dual (Conj l r) = Disj (dual l) (dual r)
dual (Disj l r) = Conj (dual l) (dual r)
dual (Neg t)    = Neg (dual t)
dual (Fn l r)   = Sub (dual r) (dual l)
dual (Sub l r)  = Fn (dual r) (dual l)

dualSeq : Sequent -> Sequent
dualSeq (Ts ls rs) = Ts (map dual rs) (map dual ls)

dualProof : LK s -> LK (dualSeq s)
dualProof  Ax                                = Ax
dualProof (Cut {g} {d} {s} {p} l r)          = 
   rewrite mapDistributesOverAppend dual d p in 
   rewrite mapDistributesOverAppend dual g s in 
   swapCtxL (map dual p) (map dual d) $ 
   swapCtxR (map dual s) (map dual g) $ 
   Cut (dualProof r) (dualProof l)
dualProof  TopR                              = BotL
dualProof  BotL                              = TopR
dualProof (ConjR l r)                        = DisjL (dualProof l) (dualProof r)
dualProof (ConjL1 p)                         = DisjR1 $ dualProof p
dualProof (ConjL2 p)                         = DisjR2 $ dualProof p
dualProof (DisjR1 p)                         = ConjL1 $ dualProof p
dualProof (DisjR2 p)                         = ConjL2 $ dualProof p
dualProof (DisjL l r)                        = ConjR (dualProof l) (dualProof r)
dualProof (NegL p)                           = NegR $ dualProof p
dualProof (NegR p)                           = NegL $ dualProof p
dualProof (ImpL {a} {b} {g} {d} {s} {p} l r) = 
   rewrite mapDistributesOverAppend dual d p in 
   rewrite mapDistributesOverAppend dual g s in 
   swapCtxL (map dual p) (map dual d) $ 
   swap3CtxR [Sub (dual b) (dual a)] (map dual s) $
   SubR (dualProof r) (dualProof l)
dualProof (ImpR p)                           = SubL $ dualProof p
dualProof (SubL p)                           = ImpR $ dualProof p
dualProof (SubR {a} {b} {g} {d} {s} {p} l r) = 
  rewrite mapDistributesOverAppend dual d p in 
  rewrite mapDistributesOverAppend dual g s in 
  swap3CtxL [Fn (dual b) (dual a)] (map dual p) $
  swapCtxR (map dual s) (map dual g) $ 
  ImpL (dualProof r) (dualProof l)
dualProof (WL p)                             = WR $ dualProof p
dualProof (CL p)                             = CR $ dualProof p
dualProof (PL {a} {b} {g} {d} {s} p)         = 
  rewrite mapDistributesOverAppend dual g (b::a::s) in 
  PR {d=map dual g} {a=dual a} {b=dual b} {s=map dual s} $ 
  rewrite sym $ mapDistributesOverAppend dual g (a::b::s) in   
  dualProof p
dualProof (WR p)                             = WL $ dualProof p
dualProof (CR p)                             = CL $ dualProof p
dualProof (PR {a} {b} {g} {d} {s} p)         = 
  rewrite mapDistributesOverAppend dual d (b::a::s) in 
  PL {g=map dual d} {a=dual a} {b=dual b} {s=map dual s} $ 
  rewrite sym $ mapDistributesOverAppend dual d (a::b::s) in 
  dualProof p
  
nonContradiction : LK ([Conj a (Neg a)] |- [])
nonContradiction = CL $ ConjL2 $ NegL $ ConjL1 Ax

excludedMiddle : LK (dualSeq ([Conj a (Neg a)] |- [])) --[] |- [Disj a (Neg a)])
excludedMiddle = dualProof nonContradiction --CR $ DisjR2 $ NegR $ DisjR1 Ax
