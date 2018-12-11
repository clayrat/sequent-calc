module ClasByNeed.Concrete.Defunctionalized

import ClasByNeed.Concrete.Syntax
import ClasByNeed.Concrete.Redex
import ClasByNeed.Concrete.Result

%default total
%access public export

-- The CPS search function, in which the continuation and demanded context have
-- been defunctionalized

data Found x a = Answer x (Term x a) a
               | Rdx (Redex x a)
               | Need x (Force x a) (Demanded x a)
               | CoNeed a (Value x a)

continue : Eq x => MetaContext x a -> Found x a -> Found x a
continue MEmpty          w =  w
continue (MLet k a c1 x) (Answer y t b) = continue k (Answer y t b)
continue (MLet k a c1 x) (Rdx r)        = continue k (Rdx r)
continue (MLet k a c1 x) (Need y f d)   = 
  if x == y
    then continue k (Rdx (ForceLet a c1 x d f))
    else continue k (Need y f (DLet a c1 x d))
continue (MLet k a c1 x) (CoNeed b v)   = continue k (CoNeed b v)

mutual
  searchCommand : Eq x => Command x a -> MetaContext x a -> Found x a
  searchCommand (C t e) k = searchContext e t k
  
  searchContext : Eq x => Context x a -> Term x a -> MetaContext x a -> Found x a 
  searchContext (Mut x c) t k = searchTermLet t x c k
  searchContext (CoVal e) t k = searchTermCoVal t e k
  
  searchTermLet : Eq x => Term x a -> x -> Command x a -> MetaContext x a -> Found x a
  searchTermLet (Mu a c1) x c k = searchCommand c (MLet k a c1 x)
  searchTermLet (Val v)   x c k = continue k (Rdx (LetVal v x c))
  
  searchTermCoVal : Eq x => Term x a -> CoValue x a -> MetaContext x a -> Found x a
  searchTermCoVal (Mu a c) e k  = continue k (Rdx (MuLazy a c e))
  searchTermCoVal (Val v)  e k   = searchCoValue e v k
  
  searchCoValue : Eq x => CoValue x a -> Value x a -> MetaContext x a -> Found x a  
  searchCoValue (CoVar a)      v k = continue k (CoNeed a v)
  searchCoValue (FLet x f tau) v k = continue k (Rdx (FLetVal v x f tau))
  searchCoValue (Fce f)        v k = searchValue v f k
  
  searchValue : Eq x => Value x a -> Force x a -> MetaContext x a -> Found x a 
  searchValue (Var x)   f k = continue k (Need x f DEmpty)
  searchValue (Lam x t) f k = searchForce f x t k
  
  searchForce : Eq x => Force x a -> x -> Term x a -> MetaContext x a -> Found x a
  searchForce (App u e)  x t k = continue k (Rdx (Beta x t u e))
  searchForce (CoFree a) x t k = continue k (Answer x t a)

search : Eq x => Command x a -> Found x a
search c = searchCommand c MEmpty
