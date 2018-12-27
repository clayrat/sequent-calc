module ClasByNeed.Closure.Translation.Translate 

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Closure.Syntax
import ClasByNeed.Closure.Substitution
import ClasByNeed.Closure.Result

%default covering
%access public export

-- The environment-based CPS transformation for \llvtall.

mutual
  transCommand : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
                 Command x a -> DenCommand x a m
  transCommand (C t e) tau = (transContext e) (transTerm t) tau
  
  transContext : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
                 Context x a -> DenContext x a m 
  transContext (Mut x c) t tau = (transCommand c) (DBind x t :: tau)
  transContext (CoVal e) t tau = t (transCoValue e) tau
  
  transTerm : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
              Term x a -> DenTerm x a m
  transTerm (Mu a c) e tau = (transCommand c) (DCoBind a e :: tau)
  transTerm (Val v)  e tau = e (transValue v) tau
  
  transCoValue : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
                 CoValue x a -> DenCoValue x a m
  transCoValue (CoVar a)       v tau = case splitAtCoVarDM a tau of
    Nothing                        => pure $ CoStuckDM a v tau
    Just (_, DBind _ _, _)         => pure $ CoStuckDM a v tau -- is this correct?
    Just (tau', DCoBind _ e, tau)  => e v (tau' ++ [DCoBind a e] ++ tau)
  transCoValue (FLet x f tau') v tau = v (transForce f) ((transEnv tau') ++ [DBind x (\e => e v)] ++ tau)
  transCoValue (Fce f)         v tau = v (transForce f) tau
  
  transValue : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
               Value x a -> DenValue x a m
  transValue {m} (Var q)   f tau = case splitAtVarDM q tau of
    Nothing                     => pure $ StuckDM q f tau
    Just (_, DCoBind _ _, _)    => pure $ StuckDM q f tau -- is this correct?
    Just (tau', DBind _ t, tau) => t (e tau') tau
  where 
    e : DenEnvironment x a m -> DenCoValue x a m
    e tau' v tau = v f (tau' ++ [DBind q (\e => e v)] ++ tau)
  transValue {m} (Lam q t) f tau = f (MkLambda lam) tau
  where 
    lam : DenTerm x a m -> DenTerm x a m
    lam u e tau' = do x' <- fresh
                      transTerm (t /// q := x') e (DBind x' u :: tau')
  
  transForce : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
               Force x a -> DenForce x a m
  transForce (App u e) (MkLambda app) tau = app (transTerm u) (transCoValue e) tau
  transForce (CoFree a) lam           tau = pure $ FinalAnswerDM lam a tau
  
  transEnv : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
             Environment x a -> DenEnvironment x a m
  transEnv = map transBinding
  
  transBinding : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
                 Binding x a -> DenBinding x a m
  transBinding (Bind x t)   = DBind x (transTerm t)
  transBinding (CoBind a e) = DCoBind a (transCoValue e)

trans : (Eq x, Eq a, Alternative m, MonadState (List x) m) =>
        Command x a -> m (ResultDM x a m)
trans c = (transCommand c) []
