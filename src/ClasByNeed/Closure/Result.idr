module ClasByNeed.Closure.Result

import ClasByNeed.List
import ClasByNeed.Closure.Syntax

%default covering
%access public export

data ResultE x a = FinalAnswerE x (Term x a) a (Environment x a)
                 | StuckE x (Force x a) (Environment x a)
                 | CoStuckE a (Value x a) (Environment x a)
         
mutual
  data ResultDM : (x : Type) -> (a : Type) -> (m : Type -> Type) -> Type where
    FinalAnswerDM : Lambda x a m -> a -> DenEnvironment x a m -> ResultDM x a m
    StuckDM : x -> DenForce x a m -> DenEnvironment x a m -> ResultDM x a m
    CoStuckDM : a -> DenValue x a m -> DenEnvironment x a m -> ResultDM x a m

  data Lambda : (x : Type) -> (a : Type) -> (m : Type -> Type) -> Type where
    MkLambda : (DenTerm x a m -> DenTerm x a m) -> Lambda x a m
  
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

splitAtCoVarDM : Eq a => a -> DenEnvironment x a m -> Maybe (DenEnvironment x a m, DenBinding x a m, DenEnvironment x a m)
splitAtCoVarDM d tau = split match tau
where 
  match : DenBinding x a m -> Bool
  match (DBind _ _)    = False
  match (DCoBind b _)  = d == b
