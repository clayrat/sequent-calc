module KSF.NaiveStack

import Data.List.Quantifiers
import KSF.ListHelp
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

repsSLComp : StateS -> Maybe Term
repsSLComp (ts,vs) = do as <- decompileV vs 
                        case decompileT ts as of 
                          Just [s] => Just s 
                          _ => Nothing

repsSLComputable : computable (NaiveStack.repsSL)  
repsSLComputable = (repsSLComp ** \(ts,vs) => aux {tsa=ts} {vsa=vs})
  where
  aux : {tsa : List Pro} -> {vsa : List Pro} -> stepFunctionAux NaiveStack.repsSL (tsa, vsa) (repsSLComp (tsa, vsa))
  aux {vsa} {tsa} with (decompileV vsa) proof dvsa
    aux {vsa} {tsa} | Just dv with (decompileT tsa dv) proof dtsa 
      aux {vsa} {tsa} | Just dv | Just []           = rewrite sym dvsa in 
                                                      \y, (_**(prf,prf1)) => 
                                                      let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
                                                      uninhabited $ justInjective $ trans dtsa prf2
      aux {vsa} {tsa} | Just dv | Just [s]          = rewrite sym dvsa in 
                                                      (dv ** (Refl, sym dtsa))
      aux {vsa} {tsa} | Just dv | Just (s1::s2::ss) = rewrite sym dvsa in 
                                                      \y, (_**(prf,prf1)) => 
                                                      let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
                                                      uninhabited $ snd $ consInjective $ justInjective $ trans dtsa prf2
      aux {vsa} {tsa} | Just dv | Nothing           = rewrite sym dvsa in 
                                                      \y, (_**(prf,prf1)) => 
                                                      let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
                                                      uninhabited $ trans dtsa prf2
    aux {vsa} {tsa} | Nothing = rewrite sym dvsa in 
                                \_, (_**(prf,_)) => uninhabited prf

decompileTaskInv : decompileT (p::ps) as = Just bs -> (as1 ** (decompile p as = Just as1, decompileT ps as1 = Just bs))
decompileTaskInv {p} {as} prf with (decompile p as)
  decompileTaskInv {p} {as} prf | Just dpas = (dpas ** (Refl, prf))
  decompileTaskInv {p} {as} prf | Nothing   = absurd prf

decompileTaskStep : decompile p as = Just bs -> decompileT (p::ps) as = decompileT ps bs
decompileTaskStep prf = rewrite prf in Refl

decompileArgInv : decompileV (p::ps) = Just as -> (s**as1**(as=Lam s::as1, decompile p [] = Just [s], decompileV ps = Just as1))
decompileArgInv {p} {ps} prf with (decompile p [])
  decompileArgInv {p} {ps} prf | Just []           = absurd prf
  decompileArgInv {p} {ps} prf | Just [ds]          with (decompileV ps)
    decompileArgInv {p} {ps} prf | Just [ds] | Just dp = (ds ** dp ** (sym $ justInjective prf, Refl, Refl))
    decompileArgInv {p} {ps} prf | Just [ds] | Nothing = absurd prf
  decompileArgInv {p} {ps} prf | Just (s1::s2::ss) = absurd prf
  decompileArgInv {p} {ps} prf | Nothing           = absurd prf

decompileArgStep : decompile p [] = Just [s] -> decompileV vs = Just as -> decompileV (p::vs) = Just (Lam s::as)  
decompileArgStep prf prf1 = 
  rewrite prf in 
  rewrite prf1 in 
  Refl

tauSimulation : repsSL (t,v) s -> StepS Tau (t,v) (t1,v1) -> repsSL (t1,v1) s  
tauSimulation {t=LamT q p :: t} (as**(repT, repV)) StepSPushVal = 
  let 
    (as1**(dlam, prf1)) = decompileTaskInv {p=LamT q p} repV
    (t1**(prf2, prf3)) = decompileLamTInv p q as as1 dlam 
   in
  (Lam t1::as ** (decompileArgStep prf2 repT, rewrite sym prf1 in decompileTaskStep prf3))
tauSimulation                   re                 StepSNil     = re

decompileArgAbstractions : decompileV vs = Just as -> All Abstraction as
decompileArgAbstractions {vs=[]}    prf = rewrite sym $ justInjective prf in []
decompileArgAbstractions {vs=v::vs} prf with (decompile v [])
  decompileArgAbstractions {vs=v::vs} prf | Just []           = absurd prf
  decompileArgAbstractions {vs=v::vs} prf | Just [ds]          with (decompileV vs) proof dvs
    decompileArgAbstractions {vs=v::vs} prf | Just [ds] | Just dv = rewrite sym $ justInjective prf in 
                                                                    IsAbstraction ds :: decompileArgAbstractions (sym dvs)
    decompileArgAbstractions {vs=v::vs} prf | Just [ds] | Nothing  = absurd prf
  decompileArgAbstractions {vs=v::vs} prf | Just (s1::s2::ss) = absurd prf
  decompileArgAbstractions {vs=v::vs} prf | Nothing           = absurd prf