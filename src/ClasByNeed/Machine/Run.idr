module ClasByNeed.Machine.Run

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Syntax
import ClasByNeed.Substitution
import ClasByNeed.Result

%access public export
%default covering

-- The abstract machine for \llvf

splitAtVar : Eq a => a -> Environment a a -> Maybe (Environment a a, Binding a a, Environment a a)
splitAtVar x tau = split (match x) tau
  where 
  match : a -> Binding a a -> Bool
  match x (Bind y _ _) = x == y

mutual 
  reduceCommand : (Eq a, Alternative m, MonadState (List a) m) =>
                  Command a a -> Environment a a -> m (ResultE a a)
  reduceCommand (C t e) tau = reduceContext e t tau
  
  reduceContext : (Eq a, Alternative m, MonadState (List a) m) =>
                   Context a a -> Term a a -> Environment a a -> m (ResultE a a)
  reduceContext (Mut x c) t tau = reduceTermLet t x c tau
  reduceContext (CoVal e) t tau = reduceTermCoVal t e tau
  
  reduceTermLet : (Eq a, Alternative m, MonadState (List a) m) =>
                  Term a a -> a -> Command a a -> Environment a a -> m (ResultE a a)
  reduceTermLet (Mu a c1) x c tau = reduceCommand c (Bind x a c1 :: tau)
  reduceTermLet (Val v)   x c tau = 
    do c' <- c // x := v
       reduceCommand c' tau
  
  reduceTermCoVal : (Eq a, Alternative m, MonadState (List a) m) =>
                    Term a a -> CoValue a a -> Environment a a -> m (ResultE a a)
  reduceTermCoVal (Mu a c) e tau = 
    do c' <- c //* a := e
       reduceCommand c' tau
  reduceTermCoVal (Val v)  e tau = reduceCoValue e v tau
  
  reduceCoValue : (Eq a, Alternative m, MonadState (List a) m) =>
                  CoValue a a -> Value a a -> Environment a a -> m (ResultE a a)
  reduceCoValue (CoVar a)       v tau = pure $ CoStuckE a v tau
  reduceCoValue (FLet x f tau') v tau = 
    do tau''  <- tau' `substEnv` (x := v)
       f'     <- f `substForce` (x := v)
       reduceValue v f' (tau'' ++ tau)
  reduceCoValue (Fce f)         v tau = reduceValue v f tau
  
  reduceValue : (Eq a, Alternative m, MonadState (List a) m) =>
                Value a a -> Force a a -> Environment a a -> m (ResultE a a)
  reduceValue (Var x)   f tau = case splitAtVar x tau of
    Nothing                      => pure $ StuckE x f tau
    Just (tau', Bind _ a c, tau) =>
      reduceCommand (C (Mu a c) (CoVal $ FLet x f tau')) tau
  reduceValue (Lam x t) f tau  = reduceForce f x t tau
  
  reduceForce : (Eq a, Alternative m, MonadState (List a) m) =>
                Force a a -> a -> Term a a -> Environment a a -> m (ResultE a a)
  reduceForce (App u e)  x t tau = 
    do x' <- fresh
       reduceCommand (C u (Mut x' (C (t /// x := x') (CoVal e)))) tau
  reduceForce (CoFree a) x t tau = pure $ FinalAnswerE x t a tau

run : (Eq a, Alternative m, MonadState (List a) m) =>
      Command a a -> m (ResultE a a)
run c = reduceCommand c []
