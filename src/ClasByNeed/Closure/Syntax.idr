module ClasByNeed.Closure.Syntax

import ClasByNeed.List

%default total
%access public export

mutual
  data Command x a = C (Term x a) (Context x a)
  
  data Term x a  = Val (Value x a)
                 | Mu a (Command x a)
  
  data Value x a  = Var x
                  | Lam x (Term x a)
  
  data Context x a  = CoVal (CoValue x a)
                    | Mut x (Command x a)
  
  data CoValue x a  = CoVar a
                    | Fce (Force x a)
                    | FLet x (Force x a) (Environment x a)
  
  data Force x a = CoFree a
                 | App (Term x a) (CoValue x a)
  
  Environment : Type -> Type -> Type
  Environment x a = List $ Binding x a
  
  data Binding x a = Bind x (Term x a) 
                   | CoBind a (CoValue x a)

splitAtVar : Eq x => x -> Environment x a -> Maybe (Environment x a, Binding x a, Environment x a)
splitAtVar q tau = split match tau
  where 
  match : Binding x a -> Bool
  match (Bind y _)   = q == y
  match (CoBind _ _) = False
