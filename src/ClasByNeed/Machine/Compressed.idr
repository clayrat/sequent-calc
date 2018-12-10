module ClasByNeed.Machine.Compressed

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Syntax
import ClasByNeed.Substitution

%access public export
%default covering

data Result x a = FinalAnswer x (Term x a) a (Environment x a)
                | Stuck x (Force x a) (Environment x a)
                | CoStuck a (Value x a) (Environment x a)

splitAtVar : Eq a => a -> Environment a a -> Maybe (Environment a a, Binding a a, Environment a a)
splitAtVar x tau = split (match x) tau
  where 
  match : a -> Binding a a -> Bool
  match x (Bind y _ _) = x == y

reduce : (Eq a, Alternative m, MonadState (List a) m) =>
         Command a a -> Environment a a -> m (Result a a)
reduce (C (Mu a c1)       (Mut x c2))               tau = reduce c2 (Bind x a c1 :: tau)
reduce (C (Val v)         (Mut x c))                tau =
  do c' <- c // x := v
     reduce c' tau
reduce (C (Mu a c)        (CoVal e))                tau = 
  do c' <- c //* a := e
     reduce c' tau
reduce (C (Val v)         (CoVal (CoVar a)))        tau = pure $ CoStuck a v tau
reduce (C (Val v)         (CoVal (FLet x f tau')))  tau = 
  do tau''  <- tau' `substEnv` (x := v)
     f'     <- f `substForce` (x := v)
     reduce (C (Val v) (CoVal (Fce f))) (tau'' ++ tau)
reduce (C (Val (Var x))   (CoVal (Fce f)))          tau = case splitAtVar x tau of
  Nothing                      => pure $ Stuck x f tau
  Just (tau', Bind _ a c, tau) => reduce (C (Mu a c) (CoVal (FLet x f tau'))) tau
reduce (C (Val (Lam x t)) (CoVal (Fce (App u e))))  tau = 
  do x' <- fresh
     reduce (C u (Mut x' (C (t /// x := x') (CoVal e)))) tau
reduce (C (Val (Lam x t)) (CoVal (Fce (CoFree a)))) tau = pure $ FinalAnswer x t a tau
  
run : (Eq a, Alternative m, MonadState (List a) m) =>
      Command a a -> m (Result a a)
run c = reduce c []
