module ClasByNeed.Concrete.Syntax

import ClasByNeed.List

%default total
%access public export

mutual
  data Command x a = C (Term x a) (Context x a)
  
  data Term x a = Val (Value x a)
                | Mu a (Command x a)
  
  data Value x a = Var x
                 | Lam x (Term x a)
  
  data Context x a = CoVal (CoValue x a)
                   | Mut x (Command x a)
  
  data CoValue x a = CoVar a
                   | Fce (Force x a)
                   | FLet x (Force x a) (Environment x a)
  
  data Force x a = CoFree a
                 | App (Term x a) (CoValue x a)
  
  Environment : Type -> Type -> Type 
  Environment x a = List $ Binding x a
  
  data Binding x a = Bind x a (Command x a)

splitAtVar : Eq a => a -> Environment a a -> Maybe (Environment a a, Binding a a, Environment a a)
splitAtVar x tau = split (match x) tau
  where 
  match : a -> Binding a a -> Bool
  match x (Bind y _ _) = x == y  