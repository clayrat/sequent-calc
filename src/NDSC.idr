module NDSC

import Data.List

%default total
%access public export

Subset : List a -> List a -> Type
Subset {a} xs ys = {x : a} -> Elem x xs -> Elem x ys

consSubset : Subset xs ys -> Subset (x::xs) (x::ys)
consSubset f  Here      = Here
consSubset f (There el) = There (f el)

contractSubset : Subset (a::a::g) (a::g)
contractSubset  Here      = Here
contractSubset (There el) = el

permuteSubset : (g : List x) -> Subset (g ++ a::b::d) (g ++ b::a::d) 
permuteSubset []       Here              = There Here
permuteSubset []      (There Here)       = Here
permuteSubset []      (There (There el)) = There $ There el
permuteSubset (g::gs)  Here              = Here
permuteSubset (g::gs) (There el)         = There $ permuteSubset gs el

data Ty = Atom | Fn Ty Ty

infix 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Fn

data Sequent = Ts (List Ty) Ty

infix 4 |-
(|-) : List Ty -> Ty -> Sequent
(|-) = Ts

data ND : Sequent -> Type where
  AxN  : Elem a g -> ND (g |- a)                      -- var
  ImpI : ND (a::g |- b) -> ND (g |- a~>b)             -- lam
  ImpE : ND (g |- a~>b) -> ND (g |- a) -> ND (g |- b) -- app

struct : Subset g g1 -> ND (g |- a) -> ND (g1 |- a)
struct f (AxN e)     = AxN $ f e
struct f (ImpI i)   = ImpI (struct (consSubset f) i)
struct f (ImpE a b) = ImpE (struct f a) (struct f b)

weaken : ND (g |- b) -> ND (a::g |- b)
weaken = struct There

contract : ND (a::a::g |- b) -> ND (a::g |- b) 
contract = struct contractSubset

permute : (g : List Ty) -> ND (g ++ a::b::d |- c) -> ND (g ++ b::a::d |- c) 
permute g = struct $ permuteSubset g

data SC : Sequent -> Type where
  AxS  : Elem a g -> SC (g |- a)     
  Cut  : SC (g |- a) -> SC (a::g |- b) -> SC (g |- b)
  ImpL : SC (g |- a) -> SC (b::g |- c) -> SC ((a~>b)::g |- c)
  ImpR : SC (a::g |- b) -> SC (g |- a ~> b)

ax0N : ND (x::xs |- x)  
ax0N = AxN Here

ax0S : SC (x::xs |- x)  
ax0S = AxS Here

nd2sc : ND s -> SC s  
nd2sc (AxN e)    = AxS e
nd2sc (ImpI i)   = ImpR $ nd2sc i
nd2sc (ImpE f g) = Cut (nd2sc f) (ImpL (nd2sc g) ax0S)

sc2nd : SC s -> ND s
sc2nd (AxS e)    = AxN e
sc2nd (Cut  l r) = ImpE (ImpI $ sc2nd r) (sc2nd l)
sc2nd (ImpL l r) = ImpE (weaken $ ImpI $ sc2nd r) (ImpE ax0N (weaken $ sc2nd l))
sc2nd (ImpR i)   = ImpI $ sc2nd i

interface Interpret (a : Type) (b : Type) where
  int : a -> b

Interpret Ty Type where
  int  Atom    = Int
  int (Fn a b) = int a -> int b

data Env : List Ty -> Type where
  Nil  : Env []
  (::) : int a -> Env g -> Env (a :: g)  

Interpret Sequent Type where
  int (Ts g a) = Env g -> int a

lookup : Elem a g -> Env g -> int a
lookup  Here      (e::_)  = e
lookup (There el) (_::es) = lookup el es

[iND] Interpret (ND s) (NDSC.int s) where
  int (AxN p)    env = lookup p env
  int (ImpI i)   env = \ia => int i (ia :: env)
  int (ImpE l r) env = (int l env) (int r env)

[iSC] Interpret (SC s) (NDSC.int s) where
  int = int @{iND} . sc2nd

-- part 2 (the lost one)

data NJ : Sequent -> Type where
  AxNJ  : NJ ([a] |- a)                     
  ImpIJ : NJ (a::g |- b) -> NJ (g |- a~>b)            
  ImpEJ : NJ (g |- a~>b) -> NJ (d |- a) -> NJ (g++d |- b)
  WNJ   : NJ (g |- b) -> NJ (a::g |- b) 
  CNJ   : NJ (a::a::g |- b) -> NJ (a::g |- b) 
  PNJ   : NJ (g ++ a::b::d |- c) -> NJ (g ++ b::a::d |- c) 

weakenCtxSubset : (g : List x) -> Subset d (g++d)
weakenCtxSubset []      el = el
weakenCtxSubset (g::gs) el = There $ weakenCtxSubset gs el

forwardHdSubset : (s : List x) -> Subset (s ++ a :: d) (a :: s ++ d)
forwardHdSubset []       el        = el
forwardHdSubset (x::_)   Here      = There Here
forwardHdSubset (_::xs) (There el) with (forwardHdSubset xs el)
  | Here      = Here
  | There el2 = There $ There el2

forwardCtxSubset : (g, s : List x) -> Subset ((g ++ s) ++ a :: d) ((g ++ a :: s) ++ d)  
forwardCtxSubset []      s  el        = forwardHdSubset s el
forwardCtxSubset (g::gs) s  Here      = Here
forwardCtxSubset (g::gs) s (There el) = There $ forwardCtxSubset gs s el

permuteCtxSubset : (g, s, p : List x) -> Subset ((g ++ s) ++ (p ++ d)) ((g ++ p) ++ (s ++ d))
permuteCtxSubset g s []      {d} el = rewrite appendNilRightNeutral g in 
                                      rewrite appendAssociative g s d in 
                                      el
permuteCtxSubset g s (p::ps) {d} el = rewrite appendAssociative g [p] ps in 
                                      permuteCtxSubset (g ++ [p]) s ps $ 
                                      rewrite sym $ appendAssociative g [p] s in
                                      forwardCtxSubset g s {d=ps++d} el

contractCtxSubset : (g : List x) -> Subset ((g ++ g) ++ d) (g ++ d)
contractCtxSubset []       el        = el
contractCtxSubset (g::gs)  Here      = Here
contractCtxSubset (g::gs) (There el) {d} with (forwardCtxSubset [] gs {a=g} {d=gs++d} $ rewrite appendAssociative gs (g::gs) d in el)
   | Here      = Here
   | There el2 = There $ contractCtxSubset gs {d} $ rewrite sym $ appendAssociative gs gs d in el2

weakenCtx : (g : List Ty) -> ND (d |- a) -> ND (g++d |- a)
weakenCtx g = struct $ weakenCtxSubset g

contractCtx : (g : List Ty) -> ND ((g++g)++d |- a) -> ND (g++d |- a)
contractCtx g = struct $ contractCtxSubset g

permuteCtx : (g, s, p : List Ty) -> ND ((g++s)++(p++d) |- a) -> ND ((g++p)++(s++d) |- a)
permuteCtx g s p = struct $ permuteCtxSubset g s p

permuteCtx' : (g, s : List Ty) -> ND ((g++s)++p |- a) -> ND ((g++p)++s |- a)
permuteCtx' g s {p} = 
  rewrite sym $ appendNilRightNeutral ((g ++ s) ++ p) in
  rewrite sym $ appendNilRightNeutral ((g ++ p) ++ s) in
  rewrite sym $ appendAssociative (g ++ s) p [] in
  rewrite sym $ appendAssociative (g ++ p) s [] in
  permuteCtx g s p {d=[]}

weakenLCtx : (g : List Ty) -> ND (g |- a) -> ND (g++d |- a)
weakenLCtx g {d} = permuteCtx' [] d {p=g} . weakenCtx d

weakenCtxJ : (g : List Ty) -> NJ (d |- a) -> NJ (g++d |- a)
weakenCtxJ []      nj = nj
weakenCtxJ (_::gs) nj = WNJ $ weakenCtxJ gs nj

forwardCtxJ : (g, s : List Ty) -> NJ ((g++s)++(a::d) |- b) -> NJ ((g++a::s)++d |- b)
forwardCtxJ g []      {a} {d} nj = 
  rewrite sym $ appendAssociative g [a] d in 
  rewrite sym $ appendNilRightNeutral g in 
  nj
forwardCtxJ g (x::xs) {a} {d} nj = 
  rewrite sym $ appendAssociative g (a::x::xs) d in 
  PNJ {a=x} {b=a} {g} {d=xs++d} $ 
  rewrite appendAssociative g [x] (a::xs ++ d) in 
  rewrite appendAssociative (g++[x]) (a::xs) d in 
  forwardCtxJ (g++[x]) xs $ 
  rewrite sym $ appendAssociative g [x] xs in
  nj

permuteCtxJ : (g, s, p : List Ty) -> NJ ((g++s)++(p++d) |- a) -> NJ ((g++p)++(s++d) |- a)
permuteCtxJ g s []      {d} nj = 
  rewrite appendNilRightNeutral g in 
  rewrite appendAssociative g s d in 
  nj
permuteCtxJ g s (p::ps) {d} nj = 
  rewrite appendAssociative g [p] ps in 
  permuteCtxJ (g++[p]) s ps $
  rewrite sym $ appendAssociative g [p] s in
  forwardCtxJ g s {a=p} {d=ps++d} nj

contractCtxJ : (g : List Ty) -> NJ ((g++g)++d |- a) -> NJ (g++d |- a)
contractCtxJ []              nj = nj
contractCtxJ (g::gs) {d} {a} nj = 
  CNJ {a=g} {g=gs++d} {b=a} $ 
  permuteCtxJ [] gs [g,g] {d} $ 
  contractCtxJ gs {d=g::g::d} $
  permuteCtxJ [] [g,g] (gs++gs) {d} $
  rewrite sym $ appendAssociative (g::g::gs) gs d in
  forwardCtxJ [] (g::gs) {a=g} {d=gs++d} $
  rewrite appendAssociative (g::gs) (g::gs) d in
  nj

permuteCtxJ' : (g, s : List Ty) -> NJ ((g++s)++p |- a) -> NJ ((g++p)++s |- a)
permuteCtxJ' g s {p} = 
  rewrite sym $ appendNilRightNeutral ((g ++ s) ++ p) in
  rewrite sym $ appendNilRightNeutral ((g ++ p) ++ s) in
  rewrite sym $ appendAssociative (g ++ s) p [] in
  rewrite sym $ appendAssociative (g ++ p) s [] in
  permuteCtxJ g s p {d=[]}

axJ : Elem a g -> NJ (g |- a)
axJ {g=g::gs}  Here      = permuteCtxJ' [] gs $ weakenCtxJ gs AxNJ
axJ           (There el) = WNJ $ axJ el

nilIN : NJ (g |- a) -> NJ (g ++ [] |- a)
nilIN {g} nj = rewrite appendNilRightNeutral g in nj

nilEN : NJ (g ++ [] |- a) -> NJ (g |- a) 
nilEN {g} nj = rewrite sym $ appendNilRightNeutral g in nj

nj2nd : NJ s -> ND s
nj2nd  AxNJ           = AxN Here
nj2nd (ImpIJ i)       = ImpI $ nj2nd i
nj2nd (ImpEJ {g} l r) = ImpE (weakenLCtx g $ nj2nd l) (weakenCtx g $ nj2nd r)
nj2nd (WNJ i)         = weaken $ nj2nd i
nj2nd (CNJ i)         = contract $ nj2nd i
nj2nd (PNJ {g} i)     = permute g $ nj2nd i

nd2nj : ND s -> NJ s
nd2nj (AxN e)        = axJ e
nd2nj (ImpI i)       = ImpIJ $ nd2nj i
nd2nj (ImpE {g} l r) = 
  nilEN $ 
  contractCtxJ {d=[]} g $ 
  nilIN {g=g++g} $ 
  ImpEJ (nd2nj l) (nd2nj r)

data LJ : Sequent -> Type where
  AxSJ  : LJ ([a] |- a)
  CutJ  : LJ (g |- a) -> LJ (a::d |- b) -> LJ (g++d |- b)
  ImpLJ : LJ (g |- a) -> LJ (b::d |- c) -> LJ ((a~>b)::g ++ d |- c)
  ImpRJ : LJ (a::g |- b) -> LJ (g |- a~>b)
  WSJ   : LJ (g |- b) -> LJ (a::g |- b)
  CSJ   : LJ (a::a::g |- b) -> LJ (a::g |- b) 
  PSJ   : LJ (g ++ a::b::d |- c) -> LJ (g ++ b::a::d |- c) 

nilIL : LJ (g |- a) -> LJ (g ++ [] |- a)
nilIL {g} lj = rewrite appendNilRightNeutral g in lj

nilEL : LJ (g ++ [] |- a) -> LJ (g |- a) 
nilEL {g} lj = rewrite sym $ appendNilRightNeutral g in lj  

lj2nj : LJ s -> NJ s
lj2nj  AxSJ           = AxNJ
lj2nj (CutJ {d} l r)  = permuteCtxJ' [] d $ ImpEJ (ImpIJ $ lj2nj r) (lj2nj l)
lj2nj (ImpLJ {d} l r) = permuteCtxJ' [] d $ ImpEJ  (ImpIJ $ lj2nj r) (ImpEJ AxNJ (lj2nj l))
lj2nj (ImpRJ i)       = ImpIJ $ lj2nj i
lj2nj (WSJ i)         = WNJ $ lj2nj i
lj2nj (CSJ i)         = CNJ $ lj2nj i
lj2nj (PSJ i)         = PNJ $ lj2nj i

nj2lj : NJ s -> LJ s
nj2lj  AxNJ       = AxSJ
nj2lj (ImpIJ i)   = ImpRJ $ nj2lj i
nj2lj (ImpEJ l r) = CutJ (nj2lj l) (nilEL $ ImpLJ (nj2lj r) AxSJ)
nj2lj (WNJ i)     = WSJ $ nj2lj i
nj2lj (CNJ i)     = CSJ $ nj2lj i
nj2lj (PNJ i)     = PSJ $ nj2lj i

lj2sc : LJ s -> SC s
lj2sc = nd2sc . nj2nd . lj2nj

sc2lj : SC s -> LJ s
sc2lj = nj2lj . nd2nj . sc2nd
