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
  StepSBetaC   : s = substP q Z r -> StepS Beta (AppT p :: t,   r :: q :: v) (s :: p :: t, v)
  StepSPushVal :                     StepS Tau  (LamT q p :: t, v)           (p :: t,      q :: v)
  StepSNil     :                     StepS Tau  (RetT :: t,     v)           (t,           v)

Uninhabited (StepS Beta (_, []) _) where
  uninhabited (StepSBetaC _) impossible

Uninhabited (StepS Beta (_, [_]) _) where
  uninhabited (StepSBetaC _) impossible

Uninhabited (StepS Tau ([], _) _) where
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

Uninhabited (StepS Tau (AppT _ :: _, _) _) where
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

Uninhabited (StepS Tau (VarT _ _ :: _, _) _) where
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

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

stepSFunctional : functional (any StepS)  
stepSFunctional x                          y                y1               (Beta**s1)           (Beta**s2)           = betaFunctional x y y1 s1 s2
stepSFunctional (AppT p :: t, r :: q :: v) (s :: p :: t, v) y1               (Beta**StepSBetaC _) (Tau**s2)            = absurd s2
stepSFunctional (AppT p :: t, r :: q :: v) y                (s :: p :: t, v) (Tau**s1)            (Beta**StepSBetaC _) = absurd s1
stepSFunctional x                          y                y1               (Tau**s1)            (Tau**s2)            = tauFunctional x y y1 s1 s2

tauTerminating : (s : StateS) -> TerminatesOn (StepS Tau) s
tauTerminating ([]            ,v) = TerminatesC $ \_,st       => absurd st
tauTerminating (RetT      ::ts,v) = assert_total $ -- TODO doesn't seem that dependent patmat kicks in here
                                    TerminatesC $ \(ts, v), StepSNil => tauTerminating (ts, v)
tauTerminating (VarT n p  ::ts,v) = TerminatesC $ \_,st       => absurd st
tauTerminating (AppT p    ::ts,v) = TerminatesC $ \_,st       => absurd st
tauTerminating (LamT p1 p2::ts,v) = assert_total $ 
                                    TerminatesC $ \(p2::ts,p1::v), StepSPushVal => tauTerminating (p2::ts,p1::v)

betaTerminating : (s : StateS) -> TerminatesOn (StepS Beta) s
betaTerminating (t,[])  = TerminatesC $ \_,st => absurd st
betaTerminating (t,[v]) = TerminatesC $ \_,st => absurd st
betaTerminating (t,r::q::v) = assert_total $ 
                              TerminatesC $ \(s::p::t, v), (StepSBetaC su) => betaTerminating (s::p::t, v)

decompileT : List Pro -> List Term -> Maybe (List Term)
decompileT []      as = Just as
decompileT (p::ps) as with (decompile p as)
  | Just as1 = decompileT ps as1
  | _        = Nothing

decompileV : List Pro -> Maybe (List Term)
decompileV []      = Just []
decompileV (v::vs) with (decompile v [], decompileV vs) 
  | (Just [s], Just as) = Just (Lam s :: as)
  | _                   = Nothing

repsSL : StateS -> Term -> Type
repsSL (ts, vs) s = (as ** (decompileV vs = Just as, decompileT ts as = Just [s]))

repsSLFunctional : functional (NaiveStack.repsSL)
repsSLFunctional (ts, vs) y y1 (as ** (prfv, prft)) (as1 ** (prfv1, prft1)) = 
  let 
    asprf = justInjective $ trans (sym prfv1) prfv
    prft2 = replace {P=\q=>decompileT ts q = Just [y1]} asprf prft1
  in 
    fst $ consInjective $ justInjective $ trans (sym prft) prft2
