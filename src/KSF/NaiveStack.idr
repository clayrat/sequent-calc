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

Uninhabited (StepS _ ([], _) _) where
  uninhabited (StepSBetaC _) impossible
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

Uninhabited (StepS Beta (_, []) _) where
  uninhabited (StepSBetaC _) impossible

Uninhabited (StepS Beta (_, [_]) _) where
  uninhabited (StepSBetaC _) impossible

Uninhabited (StepS Tau (AppT _ :: _, _) _) where
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

Uninhabited (StepS _ (VarT _ _ :: _, _) _) where
  uninhabited (StepSBetaC _) impossible
  uninhabited StepSPushVal impossible
  uninhabited StepSNil     impossible

Machine StateS where
  MRel = StepS

tauFunctional : functional (StepS Tau)
tauFunctional (LamT q p::t, v) (p::t, q::v) (p::t, q::v) StepSPushVal StepSPushVal = Refl
tauFunctional (RetT::t,     v) (t,    v)    (t,    v)    StepSNil     StepSNil     = Refl

betaFunctional : functional (StepS Beta)  
betaFunctional (AppT p :: t, r :: q :: ay) (s :: p :: t, ay)  (s1 :: p :: t, ay) (StepSBetaC su) (StepSBetaC su1) = 
  rewrite su in 
  rewrite su1 in 
  Refl

stepSFunctional : functional (any StepS)  
stepSFunctional x                    y            y1           (Beta**s1)           (Beta**s2)           = betaFunctional x y y1 s1 s2
stepSFunctional (AppT p::t, r::q::v) (s::p::t, v) y1           (Beta**StepSBetaC _) (Tau**s2)            = absurd s2
stepSFunctional (AppT p::t, r::q::v) y            (s::p::t, v) (Tau**s1)            (Beta**StepSBetaC _) = absurd s1
stepSFunctional x                    y            y1           (Tau**s1)            (Tau**s2)            = tauFunctional x y y1 s1 s2

tauTerminating : TerminatesOn (StepS Tau) s
tauTerminating {s=([]            ,v)} = TerminatesC $ \_,st       => absurd st
tauTerminating {s=(RetT      ::ts,v)} = assert_total $ -- TODO doesn't seem that dependent patmat kicks in here
                                        TerminatesC $ \(ts, v), StepSNil => tauTerminating {s=(ts, v)}
tauTerminating {s=(VarT n p  ::ts,v)} = TerminatesC $ \_,st       => absurd st
tauTerminating {s=(AppT p    ::ts,v)} = TerminatesC $ \_,st       => absurd st
tauTerminating {s=(LamT p1 p2::ts,v)} = assert_total $ 
                                        TerminatesC $ \(p2::ts,p1::v), StepSPushVal => tauTerminating {s=(p2::ts,p1::v)}

betaTerminating : TerminatesOn (StepS Beta) s
betaTerminating {s=(t,[])}      = TerminatesC $ \_,st => absurd st
betaTerminating {s=(t,[v])}     = TerminatesC $ \_,st => absurd st
betaTerminating {s=(t,r::q::v)} = assert_total $ 
                                  TerminatesC $ \(s::p::t, v), (StepSBetaC su) => betaTerminating {s=(s::p::t, v)}

decompileT : List Pro -> List Term -> Maybe (List Term)
decompileT []      as = Just as
decompileT (t::ts) as with (decompile t as)
  | Just as1 = decompileT ts as1
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
      aux {vsa} {tsa} | Just dv | Just []           = 
        rewrite sym dvsa in 
        \y, (_**(prf,prf1)) => 
        let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
        uninhabited $ justInjective $ trans dtsa prf2
      aux {vsa} {tsa} | Just dv | Just [s]          = 
        rewrite sym dvsa in 
        (dv ** (Refl, sym dtsa))
      aux {vsa} {tsa} | Just dv | Just (s1::s2::ss) = 
        rewrite sym dvsa in 
        \y, (_**(prf,prf1)) => 
        let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
        uninhabited $ snd $ consInjective $ justInjective $ trans dtsa prf2
      aux {vsa} {tsa} | Just dv | Nothing           = 
        rewrite sym dvsa in 
        \y, (_**(prf,prf1)) => 
        let prf2 = replace {P=\q=>decompileT tsa q = Just [y]} (sym $ justInjective prf) prf1 in 
        uninhabited $ trans dtsa prf2
    aux {vsa} {tsa} | Nothing = 
      rewrite sym dvsa in 
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

decompileArgEmpty : decompileV xs = Just [] -> xs = []
decompileArgEmpty {xs=[]}    prf = Refl
decompileArgEmpty {xs=x::xs} prf = 
  let (_**_**(prf1,_,_)) = decompileArgInv prf in 
  absurd prf1

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

substPRepSubst : repsP q s -> repsP r t -> decompile (substP q Z r) as = Just (subst s Z (Lam t)::as)  
substPRepSubst {q} {s} {r} {t} {as} rqs rrt = 
  decompileAppend (substP q 0 r) [] [subst s 0 (Lam t)] as $ 
  Programs.substPRepSubst q r t Z [] [s] rrt rqs

data StepLs : List Term -> List Term -> Type where
  StepLsHere  : StepL s t -> All Abstraction as -> StepLs (s::as) (t::as)
  StepLsThere : StepLs as bs -> StepLs (s::as) (s::bs)

Uninhabited (StepLs [] _) where
  uninhabited (StepLsHere _ _) impossible
  uninhabited (StepLsThere _)   impossible

Uninhabited (StepLs _ []) where
  uninhabited (StepLsHere _ _) impossible
  uninhabited (StepLsThere _)   impossible

stepLsSingletonInv : StepLs [s] bs -> (t ** (bs = [t], StepL s t))
stepLsSingletonInv (StepLsHere {t} sl []) = (t ** (Refl, sl))
stepLsSingletonInv (StepLsThere sl)       = absurd sl

stepLsDecomp : StepLs as as1 -> decompile p as = Just bs -> (bs1 ** (StepLs bs bs1, decompile p as1 = Just bs1))
stepLsDecomp                   {as1}               {p=RetT}      sls                                  prf = 
  rewrite sym $ justInjective prf in 
  (as1 ** (sls, Refl))
stepLsDecomp                                       {p=VarT n p}  sls                                  prf = 
  stepLsDecomp (StepLsThere sls) prf
stepLsDecomp                                       {p=LamT q p}  sls                                  prf with (decompile q [])
  | Just []           = absurd prf
  | Just [dq]         = stepLsDecomp (StepLsThere sls) prf
  | Just (d1::d2::ds) = absurd prf
  | Nothing           = absurd prf
stepLsDecomp {as=[]}                               {p=AppT p}    sls                                  prf = absurd prf
stepLsDecomp {as=[_]}                              {p=AppT p}    sls                                  prf = absurd prf
stepLsDecomp {as=t::s::as}     {as1=[]}            {p=AppT p}    sls                                  prf = absurd sls
stepLsDecomp {as=t::s::as}     {as1=[t]}           {p=AppT p}   (StepLsThere sls)                     prf = absurd sls
stepLsDecomp {as=t::Lam s::as} {as1=t1::Lam s::as} {p=AppT p}   (StepLsHere st (IsAbstraction s::aa)) prf = 
  stepLsDecomp (StepLsHere (StepLAppR st) aa) prf
stepLsDecomp {as=t::s::as}     {as1=t::s1::as}     {p=AppT p}   (StepLsThere (StepLsHere st aa))      prf = 
  stepLsDecomp (StepLsHere (StepLAppL st) aa) prf
stepLsDecomp {as=t::s::as}     {as1=t::s::as1}     {p=AppT p}   (StepLsThere (StepLsThere sls))       prf = 
  stepLsDecomp (StepLsThere sls) prf

stepLsDecompileTask : StepLs as as1 -> decompileT ts as = Just bs -> (bs1 ** (StepLs bs bs1, decompileT ts as1 = Just bs1))
stepLsDecompileTask {as1} {ts=[]}    sls prf = (as1 ** (rewrite sym $ justInjective prf in sls, Refl))
stepLsDecompileTask {as}  {ts=t::ts} sls prf with (decompile t as) proof dtas
  stepLsDecompileTask {as}  {ts=t::ts} sls prf | Just dt = 
    let (bs2**(sl2, repP)) = stepLsDecomp {p=t} sls (sym dtas) in 
    rewrite repP in
    stepLsDecompileTask sl2 prf
  stepLsDecompileTask {as}  {ts=t::ts} sls prf | Nothing = absurd prf 

betaSimulation : repsSL (t,v) s -> StepS Beta (t,v) (t1,v1) -> (s1 ** (repsSL (t1,v1) s1, StepL s s1))
betaSimulation     ([]             ** (_,     repT0V0)) (StepSBetaC _)                            = absurd repT0V0
betaSimulation     ([_]            ** (_,     repT0V0)) (StepSBetaC _)                            = absurd repT0V0
betaSimulation {s} ((a00::a01::a0) ** (repV1, repT0V0)) (StepSBetaC {p} {r} {q} {t=t2} {v=v1} su) = 
 let 
   (u**as1**(eqa0, repD, repV2)) = decompileArgInv {p=r} {ps=q::v1} repV1 
   (t0**a**(prf,repR,repV)) = decompileArgInv {p=q} {ps=v1} repV2
   (a1**(repPA0, repTA1)) = decompileTaskInv {p=AppT p} {as=a00::a01::a0} {ps=t2} repT0V0 
   (auprf, as1prf) = consInjective eqa0
   (t0prf, a0prf) = consInjective (trans as1prf prf)
   (b ** (redB, repB)) = stepLsDecompileTask 
           {as=App (Lam t0) (Lam u) :: a} 
           {as1=subst t0 Z (Lam u) :: a} 
           {bs=[s]} 
           {ts=p::t2} 
           (StepLsHere (StepLApp Refl) (decompileArgAbstractions repV))
           (rewrite sym auprf in 
            rewrite sym t0prf in 
            rewrite sym a0prf in 
            rewrite repPA0 in  
            repTA1) 
   (s0 ** (sprf, red1)) = stepLsSingletonInv redB
  in 
  (s0 ** ((a ** (repV, rewrite sym sprf in 
                       rewrite su in 
                       rewrite NaiveStack.substPRepSubst {q} {r} {s=t0} {t=u} {as=a} repR repD in 
                       repB)), red1))  

data StuckLs : List Term -> Type where
  StuckLsHere  : All Abstraction as -> Stuck s -> StuckLs (s::as)
  StuckLsThere : StuckLs as -> StuckLs (s::as)

Uninhabited (StuckLs []) where
  uninhabited (StuckLsHere _ _) impossible
  uninhabited (StuckLsThere _)  impossible

stuckDecompile : StuckLs as -> decompile p as = Just bs -> StuckLs bs
stuckDecompile {p=RetT}                           stls                                     prf = 
  rewrite sym $ justInjective prf in stls
stuckDecompile {p=VarT n p}                       stls                                     prf = 
  stuckDecompile (StuckLsThere stls) prf
stuckDecompile {p=AppT p}     {as=[]}             stls                                     prf = 
  absurd prf
stuckDecompile {p=AppT p}     {as=[_]}            stls                                     prf = 
  absurd prf
stuckDecompile {p=AppT p}     {as=a0::Lam s1::as} (StuckLsHere (IsAbstraction s1::aa) sa0) prf = 
  stuckDecompile (StuckLsHere aa (StuckR sa0)) prf
stuckDecompile {p=AppT p}     {as=a0::a1    ::as} (StuckLsThere (StuckLsHere aa sa1))      prf = 
  stuckDecompile (StuckLsHere aa (StuckL sa1)) prf
stuckDecompile {p=AppT p}     {as=a0::a1    ::as} (StuckLsThere (StuckLsThere stls))       prf = 
  stuckDecompile (StuckLsThere stls) prf
stuckDecompile {p=LamT p1 p2}                     stls                                     prf with (decompile p1 [])
  | Just []           = absurd prf
  | Just [qd]         = stuckDecompile (StuckLsThere stls) prf
  | Just (q1::q2::qs) = absurd prf
  | Nothing           = absurd prf

stuckDecompileTask : StuckLs as -> decompileT ts as = Just bs -> StuckLs bs 
stuckDecompileTask      {ts=[]}    stas prf = rewrite sym $ justInjective prf in stas
stuckDecompileTask {as} {ts=t::ts} stas prf with (decompile t as) proof das
  | Just d  = stuckDecompileTask (stuckDecompile stas (sym das)) prf
  | Nothing = absurd prf

stateSTrichotomy : repsSL (ts,vs) s -> Either (reducible (any StepS) (ts,vs))
                                        (Either (p**s1**((ts,vs)=([],[p]), s = Lam s1, repsP p s1))
                                                (x**p**t1**(ts = VarT x p::t1, Stuck s)))  
stateSTrichotomy {ts=[]}             {vs=[]}         (as**(h1,h2))           = 
  absurd $ trans (justInjective h1) (justInjective h2)
stateSTrichotomy {ts=[]}             {vs=v::vs}      (as**(h1,h2))           = 
  let 
    [IsAbstraction s1] = decompileArgAbstractions {vs=v::vs} (trans h1 h2) 
    (s2**as1**(prf, prf1, prf2)) = decompileArgInv {p=v} {ps=vs} (trans h1 h2) 
    (Refl,Refl) = consInjective prf
    Refl = decompileArgEmpty prf2
   in
  Right $ Left (v ** s2 ** (Refl, Refl, prf1))
stateSTrichotomy {ts=RetT      ::ts} {vs}            (as**(h1,h2))           = 
  Left ((ts,vs) ** Tau ** StepSNil)
stateSTrichotomy {ts=VarT n t  ::ts}                 (as**(h1,h2))           with (decompile t (Var n::as)) proof det
  | Just dp = 
    let aa = decompileArgAbstractions h1 in
    case stuckDecompileTask (stuckDecompile (StuckLsHere aa StuckVar) (sym det)) h2 of
      StuckLsHere [] sts => Right $ Right (n**t**ts**(Refl, sts))
      StuckLsThere stls  => absurd stls
  | Nothing = absurd h2
stateSTrichotomy {ts=AppT t    ::ts}                 ([]          **(h1,h2)) = absurd h2
stateSTrichotomy {ts=AppT t    ::ts}                 ([a]         **(h1,h2)) = absurd h2
stateSTrichotomy {ts=AppT t    ::ts} {vs=[]}         ((a1::a2::as)**(h1,h2)) = absurd $ justInjective h1
stateSTrichotomy {ts=AppT t    ::ts} {vs=[v]}        ((a1::a2::as)**(h1,h2)) with (decompile v [])
  | Just []             = absurd h1
  | Just [dv]           = absurd $ snd $ consInjective $ justInjective h1
  | Just (dv1::dv2::dv) = absurd h1
  | Nothing             = absurd h1
stateSTrichotomy {ts=AppT t    ::ts} {vs=v1::v2::vs} ((a1::a2::as)**(h1,h2)) = 
  Left ((substP v2 Z v1 :: t :: ts, vs) ** Beta ** StepSBetaC Refl)
stateSTrichotomy {ts=LamT t1 t2::ts} {vs}            (as**(h1,h2))           = 
  Left ((t2::ts, t1::vs) ** Tau ** StepSPushVal)

reducibleRed : repsSL (ts,vs) s -> reducible StepL s -> reducible (any StepS) (ts,vs)
reducibleRed rep red = 
  case stateSTrichotomy rep of 
    Left rdc                         => rdc
    Right (Left (_**_**(_,Refl,_)))  => absurd $ snd red
    Right (Right (_**_**_**(_,stk))) => absurd $ stuckNormal stk red

-- TODO reformulate originals with unsplit states?    
reducibleRed' : repsSL st s -> reducible StepL s -> reducible (any StepS) st
reducibleRed' {st=(ts,vs)} = reducibleRed

tauSimulation' : repsSL st s -> StepS Tau st st1 -> repsSL st1 s  
tauSimulation' {st=(t,v)} {st1=(t1,v1)} = tauSimulation

betaSimulation' : repsSL st s -> StepS Beta st st1 -> (s1 ** (repsSL st1 s1, StepL s s1))
betaSimulation' {st=(t,v)} {st1=(t1,v1)} = betaSimulation

stackLRefinement : refinementARS NaiveStack.repsSL    
stackLRefinement = (reducibleRed', tauSimulation', betaSimulation', \_ => tauTerminating)

compileStackL : repsSL ([compile s RetT], []) s
compileStackL {s} = ([]**(Refl, rewrite decompileCorrect s RetT [] in Refl))
