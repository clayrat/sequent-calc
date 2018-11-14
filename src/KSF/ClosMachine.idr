module KSF.ClosMachine

import Data.List
import Data.List.Quantifiers
import KSF.Prelim
import KSF.Programs
import KSF.Refinements
import KSF.NaiveStack
import KSF.Closures

%access public export
%default total

StateC : Type 
StateC = (List Clo, List Clo)

data StepC : Label -> StateC -> StateC -> Type where
  StepNil     :                        StepC Tau  (ClosC  RetT      e :: t,                   v) (                               t,              v)
  StepLoad    : index' k e = Just q -> StepC Tau  (ClosC (VarT k p) e :: t,                   v) (                  ClosC p e :: t,         q :: v)
  StepPushVal :                        StepC Tau  (ClosC (LamT q p) e :: t,                   v) (                  ClosC p e :: t, ClosC q e :: v)
  StepBetaC   :                        StepC Beta (ClosC (AppT p)   e :: t, g :: ClosC q f :: v) (ClosC q (g::f) :: ClosC p e :: t,              v)

Uninhabited (StepC _ ([], _) _) where
  uninhabited  StepNil     impossible
  uninhabited (StepLoad _) impossible
  uninhabited  StepPushVal impossible
  uninhabited  StepBetaC   impossible

Machine StateC where
  MRel = StepC

closedSC : StateC -> Type
closedSC (t, v) = (All (\z => BoundC z 0) t, All (\z => BoundC z 1) v)

repsCS : StateC -> StateS -> Type
repsCS (t, v) (t1, v1) = (closedSC (t, v), map (decompileC 0) t = t1, map (decompileC 1) v = v1)

repsCSFunctional : functional ClosMachine.repsCS
repsCSFunctional (tc,vc) (t1,v1) (t2,v2) (_, mt1, mv1) (_, mt2, mv2) = 
  rewrite sym mt1 in
  rewrite sym mt2 in
  rewrite sym mv1 in
  rewrite sym mv2 in
  Refl

cBoundCons : BoundC (ClosC p e) 1 -> BoundC d 1 -> BoundC (ClosC p (d::e)) 0  
cBoundCons (BoundCC bp f) be = BoundCC bp $ \el => case el of 
  Here => be
  There el => f el

reducibility : reducible (any StepS) (map (decompileC 0) t, map (decompileC 1) v) -> reducible (any StepC) (t,v)  
reducibility {t=[]}                                               (x1**Tau **r) = absurd r
reducibility {t=[]}                                               (x1**Beta**r) = absurd r
reducibility {t=ClosC RetT s        ::ts} {v}                     (x1**l   **r) = ((ts, v) ** Tau ** StepNil)
reducibility {t=ClosC (VarT k p) s  ::ts} {v}                     (x1**l   **r) with (index' (minus k 0) (map (decompileC 1) s)) proof idx
  reducibility {t=ClosC (VarT k p) s  ::ts} {v} (x1**Tau**r) | Just q = 
    let (y**(prf1, _)) = indexMap s (decompileC 1) (minus k 0) (sym idx) in 
    ((ClosC p s :: ts, y :: v) ** Tau ** rewrite sym $ minusZeroRight k in StepLoad prf1)
  reducibility {t=ClosC (VarT k p) s  ::ts} {v} (x1**l**r) | Nothing = absurd r
reducibility {t=ClosC (AppT x) s    ::ts} {v=[]}                  (x1**Beta**r) = absurd r
reducibility {t=ClosC (AppT x) s    ::ts} {v=[v]}                 (x1**Beta**r) = absurd r
reducibility {t=ClosC (AppT p) s    ::ts} {v=v1::ClosC vc v2::vs} (x1**l   **r) = ((ClosC vc (v1::v2) :: ClosC p s ::ts, vs) ** Beta ** StepBetaC) 
reducibility {t=ClosC (LamT p1 p2) s::ts} {v}                     (x1**l   **r) = ((ClosC p2 s ::ts, ClosC p1 s ::v) ** Tau ** StepPushVal)

closedSCPreserved : closedSC (t,v) -> any StepC (t,v) (t1,v1) -> closedSC (t1,v1)
closedSCPreserved ([],                                                  _ ) (_   **s           ) = absurd s
closedSCPreserved (br                          ::at,                    av) (Tau **StepNil     ) = (at, av)
closedSCPreserved (BoundCC (BoundPVar lt bp) f ::at,                    av) (Tau **StepLoad prf) = 
  (BoundCC bp f::at, f (indexElem prf)::av)
closedSCPreserved (BoundCC (BoundPLam bqs bp) f::at,                    av) (Tau **StepPushVal ) = 
  (BoundCC bp f::at, BoundCC bqs f::av)
closedSCPreserved (BoundCC (BoundPApp bp) fa   ::at, bg::BoundCC bc fc::av) (Beta**StepBetaC   ) = 
  (BoundCC bc (\el => case el of 
     Here => bg
     There el2 => fc el2) :: BoundCC bp fa :: at, av)
    
tauSimulation : StepC Tau (t,v) (t1,v1) -> StepS Tau (map (decompileC 0) t, map (decompileC 1) v) (map (decompileC 0) t1, map (decompileC 1) v1)     
tauSimulation  StepNil               = StepSNil
tauSimulation (StepLoad {k} {e} {q} prf) with (index' (minus k 0) (map (decompileC 1) e)) proof idx
  | Just dq  = 
      let (y**(prf1, prf2)) = indexMap e (decompileC 1) (minus k 0) (sym idx) in 
      rewrite prf2 in    
      let prf1m = replace {P=\x=>index' x e = Just y} (minusZeroRight k) prf1 in
      rewrite justInjective $ trans (sym prf) prf1m in
      StepSPushVal
  | Nothing = 
      let dq = indexMapOf e (decompileC 1) (minus k 0) (replace {P=\x=>index' x e = Just q} (sym $ minusZeroRight k) prf) in
      absurd $ trans idx dq
tauSimulation  StepPushVal           = StepSPushVal 
    
betaSimulation : closedSC (t,v) -> StepC Beta (t,v) (t1,v1) -> StepS Beta (map (decompileC 0) t, map (decompileC 1) v) (map (decompileC 0) t1, map (decompileC 1) v1)
betaSimulation (_,_::BoundCC _ fb::_) (StepBetaC {f}) = 
  StepSBetaC $ 
  substPlCons {w=map (decompileC 1) f} $ 
  allMap f (\z => BoundP z 1) (decompileC 1) $ 
  elemAll f $ 
  translateCBoundP . fb
