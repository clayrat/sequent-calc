module MuMuTilde.Rea4bis

import MuMuTilde

%default total
%access public export


-- It corresponds to this version:
-- || A → B ||_E = | A |_V × || B ||_E
--  | A × B |_V  = | A |_V × | B |_V

mutual
  intCN : (n : NegTypes) -> Type
  intCN (To a b) = (intTV a, intCV b)
  
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
envR g = intCtxt g intTV

envL : (d : Context) -> Type
envL d = intCtxt d intCV

mutual 
  reaR : (g, d : Context) -> (a : Types) -> (h : TyR g d a) -> (r : envR g) -> (s : envL d) -> intT a
  reaR g d a                (TyVarR prf)  r s = biorthT $ lookup r prf
  reaR g d (Neg (To a b))   (TyAppR t)    r s = \(u,e) => 
    let r2 = extInt r u in
    (reaR (extCtxt g a) d b t r2 s) e
  reaR g d a                (TyMuR c)     r s = \ia => 
    let s2 = extInt s ia in
    rea g (extCtxt d a) c r s2
  reaR g d (Pos (Prod a b)) (TyPairR x y) r s = \pa => 
    cut (reaR g d a x r s) (\va => cut (reaR g d b y r s) (\vb => pa (va,vb)))

  reaL : (g, d : Context) -> (a : Types) -> (h : TyL g d a) -> (r : envR g) -> (s : envL d) -> intC a
  reaL g d a                (TyVarL prf)  r s = biorthC $ lookup s prf
  reaL g d (Neg (To a b))   (TyAppL u pi) r s = \f => 
    cut (reaR g d a u r s) (\ib => cut (\ve => f (ib, ve)) (reaL g d b pi r s)) 
  reaL g d a                (TyMuL c)     r s = \ia => 
    let r2 = extInt r ia in
    rea (extCtxt g a) d c r2 s
  reaL g d (Pos (Prod a b)) (TyPairL c)   r s = \(p,q) =>
    let r2 = extInt {g=extCtxt g a} {t=b} (extInt r p) q in
    rea (extCtxt (extCtxt g a) b) d c r2 s
      
  rea : (g, d : Context) -> (h : Ty g d) -> (r : envR g) -> (s : envL d) -> Pole
  rea g d (TyCut {a} t pi) r s = cut (reaR g d a t r s) (reaL g d a pi r s)
