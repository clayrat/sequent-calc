module ClasByNeed.Closure.Machine.LiftLambda 

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Closure.Syntax
import ClasByNeed.Closure.Substitution
import ClasByNeed.Closure.Result

%default covering
%access public export

-- Lift beta reduction out of the reduction of an applicative context and into 
-- the lambda-abstraction that is applied.

mutual
  reduceCommand : (Eq x, Alternative m, MonadState (List x) m) =>
                  Command x a -> DenCommand x a m
  reduceCommand (C t e) tau = (reduceContext e) (reduceTerm t) tau
  
  reduceContext : (Eq x, Alternative m, MonadState (List x) m) =>
                  Context x a -> DenContext x a m 
  reduceContext (Mut x c) t tau = reduceCommand c (DBind x t :: tau)
  reduceContext (CoVal e) t tau = t (reduceCoValue e) tau
  
  reduceTerm : (Eq x, Alternative m, MonadState (List x) m) =>
               Term x a -> DenTerm x a m
  reduceTerm (Mu a c) e tau = reduceCommand c (DCoBind a e :: tau)
  reduceTerm (Val v)  e tau = e (reduceValue v) tau
  
  reduceCoValue : (Eq x, Alternative m, MonadState (List x) m) =>
                  CoValue x a -> DenCoValue x a m
  reduceCoValue (CoVar a)       v tau = pure $ CoStuckDM a v tau
  reduceCoValue (FLet x f tau') v tau = v (reduceForce f) (reduceEnv tau' ++ [DBind x (\e => e v)] ++ tau)
  reduceCoValue (Fce f)         v tau = v (reduceForce f) tau
  
  reduceValue : (Eq x, Alternative m, MonadState (List x) m) =>
                Value x a -> DenValue x a m
  reduceValue {m} (Var q)   f tau = case splitAtVarDM q tau of
    Nothing                     => pure $ StuckDM q f tau
    Just (_, DCoBind _ _, _)    => pure $ StuckDM q f tau -- is this correct?
    Just (tau', DBind _ t, tau) => t (e tau') tau
  where 
    e : DenEnvironment x a m -> DenCoValue x a m
    e tau' v tau = v f (tau' ++ [DBind q (\e => e v)] ++ tau)
  reduceValue {m} (Lam q t) f tau = f (MkLambda lam) tau
  where 
    lam : DenTerm x a m -> DenTerm x a m
    lam u e tau' = do x' <- fresh
                      reduceTerm (t /// q := x') e (DBind x' u :: tau')
  
  reduceForce : (Eq x, Alternative m, MonadState (List x) m) =>
                Force x a -> DenForce x a m
  reduceForce (App u e)  (MkLambda app) tau = app (reduceTerm u) (reduceCoValue e) tau
  reduceForce (CoFree a)  lam           tau = pure $ FinalAnswerDM lam a tau
  
  reduceEnv : (Eq x, Alternative m, MonadState (List x) m) =>
              Environment x a -> DenEnvironment x a m
  reduceEnv = map reduceBinding
  
  reduceBinding : (Eq x, Alternative m, MonadState (List x) m) =>
                  Binding x a -> DenBinding x a m
  reduceBinding (Bind x t)   = DBind x (reduceTerm t)
  reduceBinding (CoBind a e) = DCoBind a (reduceCoValue e)

run : (Eq x, Alternative m, MonadState (List x) m) =>
      Command x a -> m (ResultDM x a m)
run c = reduceCommand c []
  