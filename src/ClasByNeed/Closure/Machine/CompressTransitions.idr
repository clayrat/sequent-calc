module ClasByNeed.Closure.Machine.CompressTransitions

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.Closure.Syntax
import ClasByNeed.Closure.Substitution
import ClasByNeed.Closure.Result

%default covering
%access public export

-- Compressing the remaining corridor transitions in the machine.

mutual
  reduceCommand : (Eq x, Alternative m, MonadState (List x) m) =>
                  Command x a -> Environment x a -> m (ResultE x a)
  reduceCommand (C t e) tau = reduceContext e t tau
  
  reduceContext : (Eq x, Alternative m, MonadState (List x) m) =>
                   Context x a -> Term x a -> Environment x a -> m (ResultE x a)
  reduceContext (Mut x c) t tau = reduceCommand c (Bind x t :: tau)
  reduceContext (CoVal e) t tau = reduceTerm t e tau
  
  reduceTerm : (Eq x, Alternative m, MonadState (List x) m) =>
               Term x a -> CoValue x a -> Environment x a -> m (ResultE x a)
  reduceTerm (Mu a c) e tau = reduceCommand c (CoBind a e :: tau)
  reduceTerm (Val v)  e tau = reduceCoValue e v tau
  
  reduceCoValue : (Eq x, Alternative m, MonadState (List x) m) =>
                  CoValue x a -> Value x a -> Environment x a -> m (ResultE x a)
  reduceCoValue (CoVar a)       v tau = pure $ CoStuckE a v tau
  reduceCoValue (FLet x f tau') v tau = reduceValue v f (tau' ++ [Bind x (Val v)] ++ tau)
  reduceCoValue (Fce f)         v tau = reduceValue v f tau
  
  reduceValue : (Eq x, Alternative m, MonadState (List x) m) =>
                Value x a -> Force x a -> Environment x a -> m (ResultE x a)
  reduceValue (Var x) f tau    = case splitAtVar x tau of
    Nothing                    => pure $ StuckE x f tau
    Just (_, CoBind _ _, _)    => pure $ StuckE x f tau -- is this correct?
    Just (tau', Bind _ t, tau) => reduceTerm t (FLet x f tau') tau
  reduceValue (Lam x t) f tau  = reduceForce f x t tau
  
  reduceForce : (Eq x, Alternative m, MonadState (List x) m) =>
                Force x a -> x -> Term x a -> Environment x a -> m (ResultE x a)
  reduceForce (App u e)  x t tau = 
    do x' <- fresh
       reduceTerm (t /// x := x') e (Bind x' u :: tau)
  reduceForce (CoFree a) x t tau = pure $ FinalAnswerE x t a tau

run : (Eq x, Alternative m, MonadState (List x) m) =>
      Command x a -> m (ResultE x a)
run c = reduceCommand c []
