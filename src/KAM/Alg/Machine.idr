module KAM.Alg.Machine

import KAM.Alg.Terms
import KAM.Alg.Redex
import KAM.Alg.Refocus

%access public export
%default total

-- we will combine mapping App to Clapp (refocus+contract) and evaluating the first argument of Clapp 
-- into a single transition (compressing corridor transitions)
-- as a result, we will no longer add closed applications to the environment or evaluation context

-- enforce the absence of Clapp constructors on closed terms, environments, and evaluation contexts respectively
mutual
  ValidClosure : Closed s -> Type
  ValidClosure (Clos _ e)  = ValidEnv e
  ValidClosure (Clapp _ _) = Void

  ValidEnv : Env g -> Type
  ValidEnv  NE      = ()
  ValidEnv (CE e c) = (ValidEnv e, ValidClosure c)

ValidEvalCon : EvalCon s t -> Type  
ValidEvalCon  MT                  = ()
ValidEvalCon (ARG (Clos _ e) ctx) = (ValidEnv e, ValidEvalCon ctx)
ValidEvalCon (ARG (Clapp _ _) _)  = Void

-- now we can project the underlying context, environment and term from any valid closed term
getCon : (c : Closed s ** ValidClosure c) -> Con
getCon ((Clos {g} _ _) ** _)  = g
getCon ((Clapp _ _)    ** vc) = absurd vc

getEnv : (exc : (c : Closed s ** ValidClosure c)) -> Env (getCon exc)
getEnv ((Clos _ e)  ** _)  = e
getEnv ((Clapp _ _) ** vc) = absurd vc

getTm : (exc : (c : Closed s ** ValidClosure c)) -> Tm (getCon exc) s
getTm ((Clos t _)  ** _)  = t
getTm ((Clapp _ _) ** vc) = absurd vc

-- looking up a variable in a valid environment will always return a closure
getClosure : (x : Ref g s) -> (e : Env g) -> (ve : ValidEnv e) -> (c : Closed s ** ValidClosure c)
getClosure  Top    (CE _ (Clos t e) ) (_, ve) = (Clos t e ** ve)
getClosure  Top    (CE _ (Clapp _ _)) (_, v)  = absurd v
getClosure (Pop x) (CE e  _         ) (ve, _) = getClosure x e ve

-- indexed by the three arguments to the Krivine machine: a term, an environment, and an evaluation context (aka stack)
-- a constructor for every transition; recursive calls to the abstract machine correspond to recursive arguments to a constructor
data TraceM : Tm g s -> Env e -> EvalCon s t -> Type where
  DoneM   : {e : Env g} -> (body : Tm (CC g t) s) -> TraceM (Lam body) e MT
  LookupM : {ctx : EvalCon s t} -> {e : Env g} -> (x : Ref g s) -> (ve : ValidEnv e) 
         -> (let exc = getClosure x e ve in TraceM (getTm exc) (getEnv exc) ctx) -> TraceM (Var x) e ctx
  AppM    : {e : Env g} -> {ctx : EvalCon t1 t2} -> (tm1 : Tm g (Arr s t1)) -> (tm2 : Tm g s) -> TraceM tm1 e (ARG (Clos tm2 e) ctx) 
         -> TraceM (App tm1 tm2) e ctx
  BetaM   : {e : Env g} -> (ctx : EvalCon s t) -> (t1 : Tm g1 s1) -> (e1 : Env g1) -> (body : Tm (CC g s1) s) -> TraceM body (CE e (Clos t1 e1)) ctx
         -> TraceM (Lam body) e (ARG (Clos t1 e1) ctx)

-- corresponds to the Krivine abstract machine
refocusM : {tm : Tm g s} -> {ctx : EvalCon s t} -> (e : Env g) -> TraceM tm e ctx -> (c : Closed t ** Value c)
-- evaluation is finished
refocusM e (DoneM body)         = (Clos (Lam body) e ** Val (Lam body) e)
-- look up the closure that the variable refers to in the environment, and continue evaluation with that closure’s term and environment
refocusM e (LookupM x ve tr)    = refocusM (getEnv (getClosure x e ve)) tr
-- add the argument and current environment to the application context, and continue evaluating the term
refocusM e (AppM _ _ tr)        = refocusM e tr
-- the evaluation context is not empty, we can perform a beta reduction step
refocusM e (BetaM _ t1 e1 _ tr) = refocusM (CE e (Clos t1 e1)) tr

lookupClosure : (e : Env g) -> (x : Ref g s) -> (ve : ValidEnv e) 
             -> let exc = getClosure x e ve in lookup e x = Clos (getTm exc) (getEnv exc)
lookupClosure  NE                 Top     _        impossible
lookupClosure  NE                (Pop _)  _        impossible
lookupClosure (CE e (Clos t e1))  Top    (ve, ve1) = Refl
lookupClosure (CE _ (Clapp _ _))  Top    (_, v)    = absurd v
lookupClosure (CE e  _         ) (Pop x) (ve, _)   = lookupClosure e x ve

lookupLemma : (e : Env g) -> (x : Ref g s) -> (ve : ValidEnv e) -> ValidEnv (getEnv (getClosure x e ve))
lookupLemma  NE                 Top     _       impossible
lookupLemma  NE                (Pop _)  _       impossible
lookupLemma (CE _ (Clos _ e1))  Top    (_, ve1) = ve1
lookupLemma (CE _ (Clapp _ _))  Top    (_, v)   = absurd v
lookupLemma (CE e  _         ) (Pop x) (ve, _)  = lookupLemma e x ve

-- During execution, the Krivine machine only adds closures to the environment and evaluation context
terminationLemmaM : (tm : Tm g s) -> (ctx : EvalCon s t) -> (e : Env g) -> (vctx : ValidEvalCon ctx) -> (ve : ValidEnv e) -> TraceR (refocus (Clos tm e) ctx) -> TraceM tm e ctx
terminationLemmaM (Lam body)  MT                  _ ()         _   DoneR     = DoneM body
terminationLemmaM (Lam body) (ARG (Clos t e1) ec) e (ve1, vec) ve (StepR tr) = BetaM ec t e1 body $ 
                                                                               terminationLemmaM body ec (CE e (Clos t e1)) vec (ve, ve1) tr
terminationLemmaM (Lam _)    (ARG (Clapp _ _) _)  _ vctx       _   _         = absurd vctx
terminationLemmaM (App f x)  ctx                  e vctx       ve (StepR tr) = AppM f x $ 
                                                                               terminationLemmaM f (ARG (Clos x e) ctx) e (ve, vctx) ve tr
terminationLemmaM (Var i)    ctx                  e vctx       ve (StepR tr) = 
  LookupM i ve $ 
  assert_total $ terminationLemmaM (getTm $ getClosure i e ve) ctx (getEnv $ getClosure i e ve) 
                                   vctx (lookupLemma e i ve) (rewrite sym $ lookupClosure e i ve in tr)  -- TODO seems rewrite confuses totality checker

terminationM : (tm : Tm NC s) -> TraceM tm NE MT
terminationM tm = terminationLemmaM tm MT NE () () (terminationR (Clos tm NE))

evaluateM : Tm NC s -> (c : Closed s ** Value c)
evaluateM t = refocusM NE (terminationM t)

mutual 
  correctnessM : (tm : Tm g s) -> (ctx : EvalCon s v) -> (e : Env g) -> (tr : TraceM tm e ctx) -> (tr0 : TraceR (refocus (Clos tm e) ctx)) 
              -> refocusM e tr = iterateR (refocus (Clos tm e) ctx) tr0
  correctnessM (Lam body)  MT                   e (DoneM body)              DoneR      = Refl
  correctnessM (Lam body) (ARG (Clos c e1) ctx) e (BetaM ctx c e1 body tr) (StepR tr0) = correctnessM body ctx (CE e (Clos c e1)) tr tr0
  correctnessM (App f x)   ctx                  e (AppM f x tr)            (StepR tr0) = correctnessM f (ARG (Clos x e) ctx) e tr tr0
  correctnessM (Var i)     ctx                  e (LookupM i ve tr)        (StepR tr0) = auxM tr tr0

  auxM : (tr : TraceM (getTm (getClosure i e ve)) (getEnv (getClosure i e ve)) ctx) -> (tr0 : TraceR (refocus (lookup e i) ctx)) -> refocusM (getEnv (getClosure i e ve)) tr = iterateR (refocus (lookup e i) ctx) tr0   
  auxM {e} {i} {ve} {ctx} = 
    rewrite lookupClosure e i ve in 
    assert_total $ correctnessM (getTm (getClosure i e ve)) ctx (getEnv (getClosure i e ve))  -- TODO rewrite can't change argument, and pointfree confuses totality checker

corollary : (tm : Tm NC s) -> evaluateM tm = evaluateR (Clos tm NE)
corollary tm = correctnessM tm MT NE (terminationM tm) (terminationR (Clos tm NE))