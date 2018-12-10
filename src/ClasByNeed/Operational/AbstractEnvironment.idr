module ClasByNeed.Operational.AbstractEnvironment

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Syntax
import ClasByNeed.Substitution

%access public export
%default covering

-- Abstract the environment manipulation out of the interpreter loop

data Result x a = FinalAnswer x (Term x a) a (Environment x a)
                | Stuck x (Force x a) (Environment x a)
                | CoStuck a (Value x a) (Environment x a)

mutual
  refocusCommand : (Eq a, Alternative m, MonadState (List a) m) =>
                   Command a a -> Environment a a -> m (Result a a)
  refocusCommand (C t e) k = refocusContext e t k
  
  refocusContext : (Eq a, Alternative m, MonadState (List a) m) =>
                   Context a a -> Term a a -> Environment a a -> m (Result a a)
  refocusContext (Mut x c) t k = refocusTermLet t x c k
  refocusContext (CoVal e) t k = refocusTermCoVal t e k
  
  refocusTermLet : (Eq a, Alternative m, MonadState (List a) m) =>
                   Term a a -> a -> Command a a -> Environment a a -> m (Result a a)
  refocusTermLet (Mu a c1) x c k = refocusCommand c (Bind x a c1 :: k)
  refocusTermLet (Val v)   x c k = c // x := v >>= flip refocus k
  
  refocusTermCoVal : (Eq a, Alternative m, MonadState (List a) m) =>
                     Term a a -> CoValue a a -> Environment a a -> m (Result a a)
  refocusTermCoVal (Mu a c) e k = c //* a := e >>= flip refocus k
  refocusTermCoVal (Val v)  e k = refocusCoValue e v k
  
  refocusCoValue : (Eq a, Alternative m, MonadState (List a) m) =>
                   CoValue a a -> Value a a -> Environment a a -> m (Result a a)
  refocusCoValue (CoVar a)      v k = pure $ CoStuck a v k
  refocusCoValue (FLet x f tau) v k = 
    do tau'  <- tau `substEnv` (x := v)
       f'    <- f `substForce` (x := v)
       refocus (C (Val v) (CoVal $ Fce f')) (tau' ++ k)
  refocusCoValue (Fce f)        v k = refocusValue v f k
  
  refocusValue : (Eq a, Alternative m, MonadState (List a) m) =>
                 Value a a -> Force a a -> Environment a a -> m (Result a a)
  refocusValue (Var x)   f k = continue k x f
  refocusValue (Lam x t) f k = refocusForce f x t k
  
  refocusForce : (Eq a, Alternative m, MonadState (List a) m) =>
                 Force a a -> a -> Term a a -> Environment a a -> m (Result a a)
  refocusForce (App u e)  x t k = 
    do x' <- fresh
       let t' = t /// x := x'
       refocus (C u (Mut x' (C t' (CoVal e)))) k
  refocusForce (CoFree a) x t k = pure $ FinalAnswer x t a k

  refocus : (Eq a, Alternative m, MonadState (List a) m) =>
            Command a a -> Environment a a -> m (Result a a)
  refocus c k = refocusCommand c k
  
  continue : (Eq a, Alternative m, MonadState (List a) m) =>          
             Environment a a -> a -> Force a a -> m (Result a a)  
  continue k y f = case split (match y) k of
    Nothing                        => pure $ Stuck y f k
    Just (left, Bind x a c, right) => refocus (C (Mu a c) (CoVal (FLet x f left))) right
  where 
    match : a -> Binding a a -> Bool
    match y (Bind x _ _) = x == y

run : (Eq a, Alternative m, MonadState (List a) m) =>
      Command a a -> m (Result a a)
run c = refocus c []
