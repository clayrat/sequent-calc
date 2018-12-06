module ClasByNeed.Operational.Decompose

import ClasByNeed.Syntax
import ClasByNeed.Redex

%default total
%access public export

-- The decomposition of a program into the standard redex and its surrounding 
-- meta-context, if available. This is a trivial extension of the
-- defunctionalized search function.

data MetaContext x a = MEmpty
                     | MLet (MetaContext x a) a (Command x a) x

data Decomposition x a = Answer x (Term x a) a (MetaContext x a)
                       | Rdx (Redex x a) (MetaContext x a)
                       | Need x (Force x a) (Demanded x a)
                       | CoNeed a (Value x a) (MetaContext x a)

recomp : MetaContext x a -> Command x a -> Command x a                                           
recomp  MEmpty        c' = c'
recomp (MLet k a c x) c' = recomp k (C (Mu a c) (Mut x c'))

continue : Eq x => MetaContext x a -> Decomposition x a -> Decomposition x a       
continue MEmpty          w = w
continue (MLet k a c1 x) (Answer y t b k') = continue k (Answer y t b k')
continue (MLet k a c1 x) (Rdx r k')        = continue k (Rdx r k')
continue (MLet k a c1 x) (Need y f d)      = 
  if x == y 
    then continue k (Rdx (ForceLet a c1 x d f) k)
    else continue k (Need y f (DLet a c1 x d))
continue (MLet k a c1 x) (CoNeed b v k')   = continue k (CoNeed b v k')

mutual
  decompCommand : Eq x => Command x a -> MetaContext x a -> Decomposition x a                               
  decompCommand (C t e) k = decompContext e t k
  
  decompContext : Eq x => Context x a -> Term x a -> MetaContext x a -> Decomposition x a                                
  decompContext (Mut x c) t k = decompTermLet t x c k
  decompContext (CoVal e) t k = decompTermCoVal t e k
  
  decompTermLet : Eq x => Term x a -> x -> Command x a -> MetaContext x a -> Decomposition x a                               
  decompTermLet (Mu a c1) x c k = decompCommand c (MLet k a c1 x)
  decompTermLet (Val v)   x c k = continue k (Rdx (LetVal v x c) k)
  
  decompTermCoVal : Eq x => Term x a -> CoValue x a -> MetaContext x a -> Decomposition x a                               
  decompTermCoVal (Mu a c) e k = continue k (Rdx (MuLazy a c e) k)
  decompTermCoVal (Val v)  e k = decompCoValue e v k
  
  decompCoValue : Eq x => CoValue x a -> Value x a -> MetaContext x a -> Decomposition x a                               
  decompCoValue (CoVar a)      v k = continue k (CoNeed a v k)
  decompCoValue (FLet x f tau) v k = continue k (Rdx (FLetVal v x f tau) k)
  decompCoValue (Fce f)        v k = decompValue v f k
  
  decompValue : Eq x => Value x a -> Force x a -> MetaContext x a -> Decomposition x a                               
  decompValue (Var x)   f k = continue k (Need x f DEmpty)
  decompValue (Lam x t) f k = decompForce f x t k
  
  decompForce : Eq x => Force x a -> x -> Term x a -> MetaContext x a -> Decomposition x a                               
  decompForce (App u e)  x t k = continue k (Rdx (Beta x t u e) k)
  decompForce (CoFree a) x t k = continue k (Answer x t a k)

decomp : Eq x => Command x a -> Decomposition x a
decomp c = decompCommand c MEmpty
