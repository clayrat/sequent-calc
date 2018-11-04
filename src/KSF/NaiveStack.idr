module KSF.NaiveStack

import KSF.Prelim
import KSF.Lambda
import KSF.Refinements
import KSF.Programs

%access public export
%default total

StateS : Type 
StateS = (List Pro, List Pro)

data StepS : Label -> StateS -> StateS -> Type where
  StepSBetaC : s = substP q Z r -> StepS Beta (AppT p :: t, r :: q :: v) (s :: p :: t, v)
  StepSPushVal : StepS Tau (LamT q p :: t, v) (p :: t, q :: v)
  StepSNil : StepS Tau (RetT :: t, v) (t, v)

Machine StateS where
  MRel = StepS

tauFunctional : functional (StepS Tau)
tauFunctional (LamT q p :: t, v) (p :: t, q :: v) (p :: t, q :: v) StepSPushVal StepSPushVal = Refl
tauFunctional (RetT :: t, v)     (t, v)           (t, v)           StepSNil     StepSNil     = Refl

betaFunctional : functional (StepS Beta)  
betaFunctional (AppT p :: t, r :: q :: ay) (s :: p :: t, ay)  (s1 :: p :: t, ay) (StepSBetaC su) (StepSBetaC su1) = 
  rewrite su in 
  rewrite su1 in 
  Refl
