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

-- (see Rea1 - Rea4)


-- We can also imagine many different ways to define truth and falsity values
-- by mixing the previous definitions. We give a few more definitions to illustrate this.

-- (see Rea1bis - Rea4bis)