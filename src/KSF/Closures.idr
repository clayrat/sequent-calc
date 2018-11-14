module KSF.Closures

import Data.List
import Data.List.Quantifiers
import KSF.Prelim
import KSF.Programs

%access public export
%default total

data Clo = ClosC Pro (List Clo)

minusLt : LTE k n -> LT n (k+m) -> LT (n `minus` k) m
minusLt {k=Z}   {n}     lte lt = rewrite  minusZeroRight n in lt
minusLt {k=S k} {n=Z}   lte lt = absurd lte
minusLt {k=S k} {n=S n} lte lt = minusLt (fromLteSucc lte) (fromLteSucc lt)

notLTEImpliesGT : Not (LTE k n) -> GT k n
notLTEImpliesGT {k=Z}           ctr = absurd $ ctr LTEZero
notLTEImpliesGT {k=S k} {n=Z}   ctr = LTESucc LTEZero
notLTEImpliesGT {k=S k} {n=S n} ctr = LTESucc (notLTEImpliesGT (ctr . LTESucc))

substPl : Pro -> Nat -> List Pro -> Pro
substPl  RetT      k w = RetT
substPl (VarT n p) k w with (isLTE k n)
  | No _ = VarT n (substPl p k w)
  | Yes _ with (index' (n `minus` k) w)
    | Just q = LamT q (substPl p k w)
    | _      = VarT n (substPl p k w)
substPl (LamT q p) k w = LamT (substPl q (S k) w) (substPl p k w)
substPl (AppT p)   k w = AppT (substPl p k w)

substPlNil : (p : Pro) -> substPl p k [] = p
substPlNil  RetT        = Refl
substPlNil (VarT n x)  {k} with (isLTE k n)
  | No _  = cong $ substPlNil x
  | Yes _ = 
      rewrite indexNone {a=Pro} {n=n `minus` k} {l=[]} LTEZero in
      cong $ substPlNil x 
substPlNil (AppT x)      = cong $ substPlNil x
substPlNil (LamT p1 p2) {k} = 
  rewrite substPlNil p1 {k=S k} in 
  cong $ substPlNil p2

boundPMono : BoundP p k -> LTE k k1 -> BoundP p k1
boundPMono  BoundPRet           lte = BoundPRet
boundPMono (BoundPVar snk bpk)  lte = BoundPVar (lteTransitive snk lte) (boundPMono bpk lte)
boundPMono (BoundPLam bqsk bpk) lte = BoundPLam (boundPMono bqsk (LTESucc lte)) (boundPMono bpk lte)
boundPMono (BoundPApp bpk)      lte = BoundPApp (boundPMono bpk lte)

boundPSubstP : BoundP p k -> substP p k r = p
boundPSubstP      BoundPRet               = Refl
boundPSubstP {k} (BoundPVar {n} snk bpk)  with (decEq n k)
  boundPSubstP {k} (BoundPVar {k} snk bpk) | Yes Refl = absurd $ notLteSucc snk
  boundPSubstP {k} (BoundPVar {n} snk bpk) | No ctr = cong $ boundPSubstP bpk
boundPSubstP {r} (BoundPLam {p} bqsk bpk) = 
  rewrite boundPSubstP {r} bpk in
  cong {f=\z=>LamT z p} $ boundPSubstP {r} bqsk
boundPSubstP {r} (BoundPApp bpk)          = cong  $ boundPSubstP {r} bpk

substPlCons : All (\z => BoundP z 1) w -> substPl p k (q::w) = substP (substPl p (S k) w) k q
substPlCons             {p=RetT}       a = Refl
substPlCons {k} {w} {q}  {p=VarT n p}   a with (isLTE (S k) n)
  substPlCons {k} {w} {q} {p=VarT (S n) p} a | Yes (LTESucc lt) with (index' (n `minus` k) w) proof idx
    substPlCons {k} {w} {q} {p=VarT (S n) p} a | Yes (LTESucc lt) | Just t = 
      rewrite snd $ islteRight lt in 
      rewrite minusSucc lt in
      rewrite sym idx in
      rewrite boundPSubstP {p=t} {k=S k} {r=q} $ boundPMono {k1=S k} (indexAll a (sym idx)) (LTESucc LTEZero) in
      cong $ substPlCons a
    substPlCons {k} {w} {p=VarT (S n) p} a | Yes (LTESucc lt) | Nothing = 
      rewrite snd $ islteRight lt in   
      rewrite minusSucc lt in        
      rewrite sym idx in
      rewrite snd $ decNot $ lteNotEqSucc lt . sym in
      cong $ substPlCons a
  substPlCons {k} {p=VarT n p} a | No  gt with (decEq n k)
    substPlCons {k} {p=VarT k p} a | No gt | Yes Refl = 
      rewrite snd $ islteRefl {k} in 
      rewrite sym $ minusZeroN k in
      cong $ substPlCons a
    substPlCons {k} {p=VarT n p} a | No gt | No ctra = 
      rewrite snd $ islteLT $ lteNotEqLt (notLTImpliesGTE gt) ctra in 
      cong $ substPlCons a
substPlCons             {p=AppT p}     a = cong $ substPlCons a
substPlCons {k} {q} {w} {p=LamT p1 p2} a = 
  rewrite substPlCons {p=p1} {k=S k} {q} {w} a in 
  rewrite substPlCons {p=p2} {k}     {q} {w} a in 
  Refl
  
substPBoundP : All (\z => BoundP z 1) w -> BoundP p (k + length w) -> BoundP (substPl p k w) k  
substPBoundP {p=RetT}             a BoundPRet            = BoundPRet
substPBoundP {p=VarT n p} {k} {w} a (BoundPVar lt bpk)   with (isLTE k n)
  | Yes lte = 
    let (_**prf) = indexLtJust w (n `minus` k) (minusLt lte lt) in 
    rewrite prf in
    BoundPLam (boundPMono {k1=S k} (indexAll a prf) (LTESucc LTEZero)) (substPBoundP a bpk)
  | No  gt  = BoundPVar (notLTEImpliesGT gt) (substPBoundP a bpk)
substPBoundP {p=AppT p}           a (BoundPApp bpk)      = BoundPApp (substPBoundP a bpk)
substPBoundP {p=LamT p1 p2}       a (BoundPLam bqsk bpk) = BoundPLam (substPBoundP a bqsk) (substPBoundP a bpk)

decompileC : Nat -> Clo -> Pro
decompileC k (ClosC c e) = substPl c k (assert_total $ map (decompileC 1) e)

data BoundC : Clo -> Nat -> Type where
  BoundCC : BoundP p (k+length e) -> ({x : Clo} -> Elem x e -> BoundC x 1) -> BoundC (ClosC p e) k

translateCBoundP : BoundC e k -> BoundP (decompileC k e) k  
translateCBoundP {e=ClosC p e} (BoundCC bp f) = 
  substPBoundP {p} {w = map (decompileC 1) e} 
    (allMap e (\z => BoundP z 1) (decompileC 1) (elemAll e (assert_total $ translateCBoundP . f)))
    (rewrite mapPreservesLength (decompileC 1) e in bp)
