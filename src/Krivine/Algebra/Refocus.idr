module Krivine.Algebra.Refocus

import Krivine.Algebra.Terms
import Krivine.Algebra.Redex
import Krivine.Algebra.Iterated

%access public export
%default total

-- a small-step abstract machine that is not yet tail-recursive
-- but forms a convenient halfway point between the small step evaluator and the Krivine machine

-- instead of repeatedly plugging and decomposing, navigate directly to the next redex
refocus : (c : Closed s) -> (ctx : EvalCon s t) -> Decomposition (plug c ctx)
refocus (Clos (Lam body) env)  MT         = DecompVal body env
refocus (Clos (Lam body) env) (ARG cl ct) = Decompose (Beta body env cl) ct
refocus (Clos (App f x) env)   ctx        = Decompose (Rapp f x env) ctx
refocus (Clos (Var i) env)     ctx        = Decompose (Lookup i env) ctx
refocus (Clapp c1 c2)          ctx        = refocus c1 (ARG c2 ctx)

refocusCorrect : (c : Closed s) -> (ctx : EvalCon s t) -> refocus c ctx = decompose (plug c ctx)
refocusCorrect (Clos (Lam body) env)  MT         = Refl
refocusCorrect (Clos (Lam body) env) (ARG cl ct) = sym $ decomposePlug (Clos (Lam body) env) (ARG cl ct) 
refocusCorrect (Clos (App f x) env)   MT         = Refl
refocusCorrect (Clos (App f x) env)  (ARG cl ct) = sym $ decomposePlug (Clos (App f x) env) (ARG cl ct) 
refocusCorrect (Clos (Var i) env)     MT         = Refl
refocusCorrect (Clos (Var i) env)    (ARG cl ct) = sym $ decomposePlug (Clos (Var i) env) (ARG cl ct) 
refocusCorrect (Clapp c1 c2)          ctx        = refocusCorrect c1 (ARG c2 ctx)

data TraceR : Decomposition c -> Type where
  DoneR : {body : Tm (CC g s) t} -> {e : Env g} -> TraceR (DecompVal body e)
  StepR : TraceR (refocus (contract r) ctx) -> TraceR (Decompose r ctx)

collapsibleR : (d : Decomposition c) -> (t1, t2 : TraceR d) -> t1 = t2 
collapsibleR (DecompVal _ _)    DoneR      DoneR = Refl
collapsibleR (Decompose r ctx) (StepR t1) (StepR t2) = cong $ collapsibleR (refocus (contract r) ctx) t1 t2

terminationLemma : Trace (decompose c) -> TraceR (decompose c)
terminationLemma {c} tr with (decompose c)
  terminationLemma tr        | DecompVal body e = DoneR
  terminationLemma (Step tr) | Decompose r ctx  = 
    StepR $ rewrite refocusCorrect (contract r) ctx in 
            terminationLemma tr

terminationR : (c : Closed s) -> TraceR (refocus c MT)
terminationR c = 
  rewrite refocusCorrect c MT in 
  terminationLemma (termination c)

--  repeatedly refocuse and contract until a value has been reached  
iterateR : {c : Closed s} -> (d : Decomposition c) -> TraceR d -> (c1 : Closed s ** Value c1)  
iterateR (DecompVal body e) DoneR     = (Clos (Lam body) e ** Val (Lam body) e)
iterateR (Decompose r ctx) (StepR tr) = iterateR (refocus (contract r) ctx) tr

evaluateR : Closed s -> (c1 : Closed s ** Value c1)
evaluateR c = iterateR (refocus c MT) (terminationR c)

mutual 
  correctnessLemma : {c : Closed s} -> (tr : TraceR (decompose c)) -> (tr0 : Trace (decompose c)) 
                  -> iterateR (decompose c) tr = iterate (decompose c) tr0
  correctnessLemma {c} tr tr0 with (decompose c)
    correctnessLemma {c=Clos (Lam body) e}       DoneR      Done      | DecompVal body e = Refl
    correctnessLemma {c=plug (fromRedex r) ctx} (StepR tr) (Step tr0) | Decompose r ctx  = aux tr tr0
    
  aux : (tr : TraceR (refocus (contract r) ctx)) -> (tr0 : Trace (decompose (plug (contract r) ctx))) 
     -> iterateR (refocus (contract r) ctx) tr = iterate (decompose (plug (contract r) ctx)) tr0
  aux {r} {ctx} = 
    rewrite refocusCorrect (contract r) ctx in 
    assert_total $ correctnessLemma   -- TODO rewrite can't change argument, and pointfree confuses totality checker

correctness : {c : Closed s} -> (tr : TraceR (refocus c MT)) -> (tr0 : Trace (decompose c)) 
           -> iterateR (refocus c MT) tr = iterate (decompose c) tr0
correctness {c} = 
  rewrite refocusCorrect c MT in 
  correctnessLemma
    
corollary : (c : Closed s) -> evaluateR c = evaluate c
corollary c = correctness (terminationR c) (termination c)