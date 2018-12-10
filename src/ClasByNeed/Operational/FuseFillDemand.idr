module ClasByNeed.Operational.FuseFillDemand

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Syntax
import ClasByNeed.Substitution

%access public export
%default covering

-- Fuse the recomposition of demanded meta-contexts into the mutually
-- recursive interpreter

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
    -- |refocus (fillDemand (tau // (x, v)) c') k|
    -- |  where c' = C (Val v) (CoVal (Force (f // (x, v))))|
    do tau' <- tau `substEnv` (x := v)
       f' <- f `substForce` (x := v)
       fillDemand tau' (C (Val v) (CoVal (Fce f))) k
  refocusCoValue (Fce f)        v k = refocusValue v f k
  
  refocusValue : (Eq a, Alternative m, MonadState (List a) m) =>
                 Value a a -> Force a a -> Environment a a -> m (Result a a)
  refocusValue (Var x)   f k = continue k x f empty
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
             Environment a a -> a -> Force a a -> Environment a a -> m (Result a a)  
  continue []                 y f d = pure $ Stuck y f d
  continue (Bind x a c :: k') y f d = 
    if x == y 
      then refocus (C (Mu a c) (CoVal (FLet x f d))) k'
      else continue k' y f (d |> Bind x a c)

  fillDemand : (Eq a, Alternative m, MonadState (List a) m) =>
               Environment a a -> Command a a -> Environment a a -> m (Result a a)
  fillDemand d c' k = case viewr d of
    EmptyR                => refocus c' k
    ConsR d' (Bind x a c) =>
      -- |refocus (C (Mu a c) (Let x (fillDemand d' c'))) k|
      -- |refocusContext (Let x (fillDemand d' c')) (Mu a c) k|
      -- |refocusTermLet (Mu a c) x (fillDemand d' c') k|
      -- |refocusCommand (fillDemand d' c') (Bind x a c : k)|
      fillDemand d' c' (Bind x a c :: k)

run : (Eq a, Alternative m, MonadState (List a) m) =>
      Command a a -> m (Result a a)
run c = refocus c []
