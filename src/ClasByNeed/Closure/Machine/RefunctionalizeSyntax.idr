module ClasByNeed.Closure.Machine.RefunctionalizeSyntax

import ClasByNeed.List
import ClasByNeed.Closure.Syntax

%default covering
%access public export

-- Refunctionalizing the syntax in the machine by partially applying the
-- reduction function to syntactic expressions as soon as they become available 
-- in the interpreter.

mutual
  data ResultD x a = FinalAnswer (Lambda x a) a (DenEnvironment x a)
                   | Stuck x (DenForce x a) (DenEnvironment x a)
                   | CoStuck a (DenValue x a) (DenEnvironment x a)
  
  data Lambda x a = MkLambda x (DenTerm x a)                
  
  DenEnvironment : Type -> Type -> Type
  DenEnvironment x a = List $ DenBinding x a
  
  data DenBinding x a = DBind x (DenTerm x a) 
                      | DCoBind a (DenCoValue x a)
  
  DenTerm : Type -> Type -> Type
  DenTerm x a = DenCoValue x a -> DenEnvironment x a -> ResultD x a
  
  DenCoValue : Type -> Type -> Type
  DenCoValue x a = DenValue x a -> DenEnvironment x a -> ResultD x a
  
  DenValue : Type -> Type -> Type
  DenValue x a = DenForce x a -> DenEnvironment x a -> ResultD x a
  
  DenForce : Type -> Type -> Type
  DenForce x a = Lambda x a -> DenEnvironment x a -> ResultD x a

DenCommand : Type -> Type -> Type
DenCommand x a = DenEnvironment x a -> ResultD x a

DenContext : Type -> Type -> Type
DenContext x a = DenTerm x a -> DenEnvironment x a -> ResultD x a

splitAtVar : Eq x => x -> DenEnvironment x a -> Maybe (DenEnvironment x a, DenBinding x a, DenEnvironment x a)
splitAtVar q tau = split match tau
  where 
  match : DenBinding x a -> Bool
  match (DBind y _)   = q == y
  match (DCoBind _ _) = False

mutual
  reduceCommand : Eq x => Command x a -> DenCommand x a
  reduceCommand (C t e) tau = (reduceContext e) (reduceTerm t) tau
  
  reduceContext : Eq x => Context x a -> DenContext x a
  reduceContext (Mut x c) t tau = reduceCommand c (DBind x t :: tau)
  reduceContext (CoVal e) t tau = t (reduceCoValue e) tau
  
  reduceTerm : Eq x => Term x a -> DenTerm x a
  reduceTerm (Mu a c) e tau = reduceCommand c (DCoBind a e :: tau)
  reduceTerm (Val v)  e tau = e (reduceValue v) tau
  
  reduceCoValue : Eq x => CoValue x a -> DenCoValue x a
  reduceCoValue (CoVar a)       v tau = CoStuck a v tau
  reduceCoValue (FLet x f tau') v tau = v (reduceForce f) (reduceEnv tau' ++ [DBind x (\e => e v)] ++ tau)
  reduceCoValue (Fce f)         v tau = v (reduceForce f) tau
  
  reduceValue : Eq x => Value x a -> DenValue x a
  reduceValue (Var q)   f tau  = case splitAtVar q tau of
    Nothing                     => Stuck q f tau
    Just (_, DCoBind _ _, _)    => Stuck q f tau -- is this correct?
    Just (tau', DBind _ t, tau) => t (e tau') tau
  where 
    e : DenEnvironment x a -> DenCoValue x a
    e tau' v tau = v f (tau' ++ [DBind q (\e => e v)] ++ tau)
  reduceValue (Lam x t) f tau = f (MkLambda x (reduceTerm t)) tau
  
  reduceForce : Eq x => Force x a -> DenForce x a
  reduceForce (App u e) (MkLambda x t) tau =
    t (reduceCoValue e) (DBind x (reduceTerm u) :: tau) -- Unhygenic
  reduceForce (CoFree a) lam           tau = FinalAnswer lam a tau
  
  reduceEnv : Eq x => Environment x a -> DenEnvironment x a
  reduceEnv = map reduceBinding
  
  reduceBinding : Eq x => Binding x a -> DenBinding x a
  reduceBinding (Bind x t)   = DBind x (reduceTerm t)
  reduceBinding (CoBind a e) = DCoBind a (reduceCoValue e)

run : Eq x => Command x a -> ResultD x a
run c = reduceCommand c []

