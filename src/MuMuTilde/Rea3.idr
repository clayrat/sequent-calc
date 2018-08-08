module MuMuTilde.Rea3

import MuMuTilde

%default total
%access public export

-- Version (3): Call-by-name arrow type, call-by-value product type
-- It corresponds to this version:
-- || A → B ||   = | A | × || B ||
--  | A × B |_V  = | A |_V × | B |_V

mutual
  intCN : (n : NegTypes) -> Type
  intCN (To a b) = (intT a, intC b)
  
  intTP : (p : PosTypes) -> Type
  intTP (Prod a b) = (intTV a, intTV b)
  
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

biorthC : intCV t -> intC t
biorthC {t=Pos _} = id
biorthC {t=Neg _} = biorth

biorthT : intTV t -> intT t
biorthT {t=Pos _} = biorth
biorthT {t=Neg _} = id    

cut : intT t -> intC t -> Pole
cut {t=Pos _} s e = s e
cut {t=Neg _} s e = e s  

envR : (g : Context) -> Type
envR g = intCtxt g intT

envL : (d : Context) -> Type
envL d = intCtxt d intC

mutual 
  reaR : (g, d : Context) -> (a : Types) -> (h : TyR g d a) -> (r : envR g) -> (s : envL d) -> intT a
  reaR g d a                (TyVarR prf)  r s = lookup r prf
  reaR g d (Neg (To a b))   (TyAppR t)    r s = \(u,e) => 
  -- This suggests that: <λx.t|u.e> → <t[u/x]|e> for any u, this is call-by-name fashion for the arrow type.
    let r2 = extInt r u in
    cut (reaR (extCtxt g a) d b t r2 s) e
  reaR g d a                (TyMuR c)     r s = \ia => 
    let s2 = extInt s $ biorthC ia in
    rea g (extCtxt d a) c r s2
  reaR g d (Pos (Prod a b)) (TyPairR x y) r s = \pa => 
    -- This suggests that when considering pairs, each of their components have to be evaluated first: 
    -- this is a call-by-value fashion (for positive types).
    -- Given as a CPS translation, this would give: [(p,q)] k = [p] (λa. [q]  (λb. k (a,b) ))
    cut (reaR g d a x r s) (\va => cut (reaR g d b y r s) (\vb => pa (va,vb)))
  
  reaL : (g, d : Context) -> (a : Types) -> (h : TyL g d a) -> (r : envR g) -> (s : envL d) -> intC a
  reaL g d a                (TyVarL prf)  r s = lookup s prf
  reaL g d (Neg (To a b))   (TyAppL u pi) r s = \t => t (reaR g d a u r s, reaL g d b pi r s)
  reaL g d a                (TyMuL c)     r s = \ia => 
    let r2 = extInt r $ biorthT ia in
    rea (extCtxt g a) d c r2 s
  reaL g d (Pos (Prod a b)) (TyPairL c)   r s = \(p,q) =>
  -- We observe here that contexts of the shape µ~(x,y).c indeed expect pairs of values to reduce, 
  -- as witnessed by the fact that this values are applied biorthT
    let r2 = extInt {g=extCtxt g a} {t=b} (extInt r (biorthT {t=a} p)) (biorthT {t=b} q) in
    rea (extCtxt (extCtxt g a) b) d c r2 s
  
  rea : (g, d : Context) -> (h : Ty g d) -> (r : envR g) -> (s : envL d) -> Pole
  rea g d (TyCut {a} t pi) r s = cut (reaR g d a t r s) (reaL g d a pi r s)