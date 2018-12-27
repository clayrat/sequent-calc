module ClasByNeed.Closure.Machine.RestoreHygiene

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Closure.Syntax
import ClasByNeed.Closure.Substitution

%default covering
%access public export

-- Restore lost hygene by abstracting reduced $\lambda$-abstractions over the 
-- variable they bind.

mutual
  data ResultDM : (x : Type) -> (a : Type) -> (m : Type -> Type) -> Type where
    FinalAnswerDM : Lambda x a m -> a -> DenEnvironment x a m -> ResultDM x a m
    StuckDM : x -> DenForce x a m -> DenEnvironment x a m -> ResultDM x a m
    CoStuckDM : a -> DenValue x a m -> DenEnvironment x a m -> ResultDM x a m

  data Lambda : (x : Type) -> (a : Type) -> (m : Type -> Type) -> Type where
    MkLambda : (x -> DenTerm x a m) -> Lambda x a m
  
  DenEnvironment : Type -> Type -> (Type -> Type) -> Type
  DenEnvironment x a m = List (DenBinding x a m)
  
  data DenBinding : (x : Type) -> (a : Type) -> (m : Type -> Type) -> Type where
    DBind : x -> DenTerm x a m -> DenBinding x a m
    DCoBind : a -> DenCoValue x a m -> DenBinding x a m
  
  DenTerm : Type -> Type -> (Type -> Type) -> Type
  DenTerm x a m = DenCoValue x a m -> DenEnvironment x a m -> m (ResultDM x a m)

  DenCoValue : Type -> Type -> (Type -> Type) -> Type
  DenCoValue x a m = DenValue x a m -> DenEnvironment x a m -> m (ResultDM x a m)

  DenValue : Type -> Type -> (Type -> Type) -> Type
  DenValue x a m = DenForce x a m -> DenEnvironment x a m -> m (ResultDM x a m)

  DenForce : Type -> Type -> (Type -> Type) -> Type
  DenForce x a m = Lambda x a m -> DenEnvironment x a m -> m (ResultDM x a m)

DenCommand : Type -> Type -> (Type -> Type) -> Type
DenCommand x a m = DenEnvironment x a m -> m (ResultDM x a m)

DenContext : Type -> Type -> (Type -> Type) -> Type
DenContext x a m = DenTerm x a m -> DenEnvironment x a m -> m (ResultDM x a m)

splitAtVarDM : Eq x => x -> DenEnvironment x a m -> Maybe (DenEnvironment x a m, DenBinding x a m, DenEnvironment x a m)
splitAtVarDM q tau = split match tau
  where 
  match : DenBinding x a m -> Bool
  match (DBind y _)   = q == y
  match (DCoBind _ _) = False       

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
    lam : x -> DenTerm x a m
    lam x' = reduceTerm (t /// q := x')
  
  reduceForce : (Eq x, Alternative m, MonadState (List x) m) =>
                Force x a -> DenForce x a m
  reduceForce (App u e) (MkLambda app) tau = 
    do x' <- fresh
       app x' (reduceCoValue e) (DBind x' (reduceTerm u) :: tau)
  reduceForce (CoFree a) lam           tau = pure $ FinalAnswerDM lam a tau
  
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
