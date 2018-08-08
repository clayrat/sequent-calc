module MuMuTilde

-- port of https://www.irif.fr/~emiquey/these/real/Real.MuMutilde.html

%default total
%access public export

-- We represent derivations of propositional logic through an inductive type. 

-- Types
-- We distinguish positive types (here, the product type) and negative types (here, the arrow type). 

mutual 
  data Types : Type where
    Pos : PosTypes -> Types
    Neg : NegTypes -> Types
    
  data PosTypes : Type where
    Prod : Types -> Types -> PosTypes
    
  data NegTypes : Type where
    To : Types -> Types -> NegTypes

-- Contexts
-- Context are defined as usual, as a partial function from variables to types. We then provide some generic (toy) operations over environments.     

Context : Type
Context = Nat -> Maybe Types

extCtxt : Context -> Types -> Context
extCtxt g a  Z    = Just a 
extCtxt g a (S n) = g n

intCtxt : (g : Context) -> (i : Types -> Type) -> Type
intCtxt g i = (v : Nat) -> (t : Types) -> g v = Just t -> i t

lookup : (p : intCtxt g i) -> (q : g n = Just t) -> i t
lookup {n} {t} p q = p n t q

extInt : (p : intCtxt g i) -> (it : i t) -> intCtxt (extCtxt g t) i
extInt {g} {t} p it  Z    t Refl = it
extInt {g} {t} p it (S v) t1 prf = p v t1 prf

-- Typing judgments
-- The type system is coded by an inductive family.

mutual
  data Ty : (g, d : Context) -> Type where
    --  Γ ⊢ p:A | Δ  →  Γ | e:A ⊢ Δ → <p|e>: (Γ⊢Δ)  
    TyCut : TyR g d a -> TyL g d a -> Ty g d

  data TyR : (g, d : Context) -> Types -> Type where
    --  (a:A) ∈ Γ     →  Γ ⊢ a:A | Δ 
   TyVarR : g k = Just a -> TyR g d a
    --  Γ,a:A ⊢ p:B | Δ  →  Γ ⊢ λa.p:(A ⇒ B)  
   TyAppR : TyR (extCtxt g a) d b -> TyR g d (Neg (a `To` b))
   --  c: (Γ ⊢ Δ,α:A)  →  Γ ⊢ µα.c:A | Δ  
   TyMuR : Ty g (extCtxt d a) -> TyR g d a
   --  Γ ⊢ p:A | Δ  →  Γ ⊢ q:B | Δ → Γ ⊢ (p,q):A x B | Δ  
   TyPairR : TyR g d a -> TyR g d b -> TyR g d (Pos (a `Prod` b))

  data TyL : (g, d : Context) -> Types -> Type where
   TyVarL : d k = Just a -> TyL g d a
   TyAppL : TyR g d a -> TyL g d b -> TyL g d (Neg (a `To` b))
   TyMuL : Ty (extCtxt g a) d -> TyL g d a
   TyPairL : Ty (extCtxt (extCtxt g a) b) d -> TyL g d (Pos (a `Prod` b))

-- Realizability
-- We define a realizability interpretation of this calculus, parametrically with respect to the pole.

-- Generic realizability structure

-- We are parametric in the pole:

-- For example, we could take `pole = Void` which would give a Tarsky-style semantics, 
Pole : Type
Pole = Void

-- or we could take ``pole := { c: Tm & value c }` which would be closer to a "real" realizability interpretation.

orth : (t : Type) -> Type
orth t = t -> Pole

biorth : (x : t) -> orth (orth t) 
biorth x k = k x

--  intCV : Types -> Type
--  intTV : Types -> Type
--  envR : Context -> Type
--  envL : Context -> Type
--  reaR : TyR g d a -> envR g -> envL d -> orth (intCV a)
--  reaL : TyL g d a -> envR g -> envL d -> orth (intTV a)

namespace Rea1
-- Version (1): call-by-name
-- It corresponds to this version:
-- || A → B ||_E = | A | × || B ||
-- | A × B |_V  = | A | × | B |

  mutual
    intCN : (n : NegTypes) -> Type
    intCN (To a b) = (intT a, intC b)
  
    intTP : (p : PosTypes) -> Type
    intTP (Prod a b) = (intT a, intT b)
  
    intCV : Types -> Type 
    intCV (Neg n) = intCN n
    intCV (Pos p) = orth (intTP p)
  
    intTV : Types -> Type 
    intTV (Pos p) = intTP p
    intTV (Neg n) = orth (intCN n)
  
    intT : Types -> Type
    intT t = orth (intCV t)
  
    intC : Types -> Type
    intC t = orth (intTV t)
  
  -- We witness the (usual) inclusions between orthogonals:
  
  biorthC : intCV t -> intC t
  biorthC {t=Pos _} = id
  biorthC {t=Neg _} = biorth
  
  biorthT : intTV t -> intT t
  biorthT {t=Pos _} = biorth
  biorthT {t=Neg _} = id
  
  -- And a cut (ie. function application) whose behavior depends on the polarity:
  
  cut : intT t -> intC t -> Pole
  cut {t=Pos _} s e = s e
  cut {t=Neg _} s e = e s
  
  envR : (g : Context) -> Type
  envR g = intCtxt g intT
  
  envL : (d : Context) -> Type
  envL d = intCtxt d intC

  mutual 
    reaR : (g, d : Context) -> (a : Types) -> (h : TyR g d a) -> (p : envR g) -> (s : envL d) -> intT a
    reaR g d a                (TyVarR prf)  p s = lookup p prf
    reaR g d (Neg (To a b))   (TyAppR t)    p s = \(u,e) => 
    -- This suggests that: <λx.t|u.e> → <t[u/x]|e> for any u, this is call-by-name fashion
      let p2 = extInt p u in
      cut (reaR (extCtxt g a) d b t p2 s) e
    reaR g d a                (TyMuR c)     p s = \ia => 
      let s2 = extInt s $ biorthC ia in
      rea g (extCtxt d a) c p s2
    reaR g d (Pos (Prod a b)) (TyPairR x y) p s = \pa => pa (reaR g d a x p s, reaR g d b y p s)

    reaL : (g, d : Context) -> (a : Types) -> (h : TyL g d a) -> (p : envR g) -> (s : envL d) -> intC a
    reaL g d a                (TyVarL prf)  p s = lookup s prf
    reaL g d (Neg (To a b))   (TyAppL u pi) p s = \t => t (reaR g d a u p s, reaL g d b pi p s)
    reaL g d a                (TyMuL c)     p s = \ia => 
      let p2 = extInt p $ biorthT ia in
      rea (extCtxt g a) d c p2 s
    reaL g d (Pos (Prod a b)) (TyPairL c)   p s = \(r,q) =>
    -- This suggests that: <(t,u)|µ~(x,y).c> → c[t/x,u/x] for any t,u, this is again call-by-name fashion
      let p2 = extInt {g = extCtxt g a} {t = b} (extInt p r) q in
      rea (extCtxt (extCtxt g a) b) d c p2 s

    rea : (g, d : Context) -> (h : Ty g d) -> (p : envR g) -> (s : envL d) -> Pole
    rea g d (TyCut {a} t pi) p s = cut (reaR g d a t p s) (reaL g d a pi p s)
