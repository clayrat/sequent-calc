module ClasByNeed.Closure.Substitution.ConcreteClosure

import ClasByNeed.Closure.Syntax

%default covering
%access public export

data Subst a b = Sub a b

infix 5 :=
(:=) : a -> b -> Subst a b
(:=) = Sub

total
matchBind : Eq x => Binding x a -> Subst x b -> Bool 
matchBind (Bind x _ ) (Sub y _) = x == y
matchBind (CoBind _ _) _        = False

total
under : Eq a => (con : a -> c -> d) -> a 
             -> (sub : c -> Subst a b -> c) -> c 
             -> Subst a b -> d
under con x sub m s@(Sub y _) = 
  if (x == y) 
    then con x m
    else con x (sub m s)

total
under2 : Eq a => (con : a -> c -> d -> p) -> a 
              -> (sub1 : c -> Subst a b -> c) -> c 
              -> (sub2 : d -> Subst a b -> d) -> d 
              -> Subst a b -> p                       
under2 con x sub1 m1 sub2 m2 s@(Sub y _) =
  if (x == y) 
    then con x m1 m2
    else con x (sub1 m1 s) (sub2 m2 s)
    
total
replaceBy : Eq a => (b -> p) -> (a -> p) -> a -> Subst a b -> p 
replaceBy sub con x (Sub y m) = 
  if (x == y) 
    then sub m
    else con x

total
replace : Eq a => (a -> b) -> a -> Subst a b -> b
replace = replaceBy id    

total
mapUntil : (a -> Bool) -> (a -> a) -> List a -> List a
mapUntil p f []      = []
mapUntil p f (x::xs) = 
  if p x 
    then f x :: xs
    else f x :: mapUntil p f xs

mutual
  rename : Eq x => Command x a -> Subst x x -> Command x a 
  rename (C t e) s = C (renameTerm t s) (renameContext e s)
  
  renameTerm : Eq x => Term x a -> Subst x x -> Term x a
  renameTerm (Val v)  s = Val $ renameValue v s
  renameTerm (Mu a c) s = Mu a (rename c s)
  
  renameValue : Eq x => Value x a -> Subst x x -> Value x a
  renameValue (Var x)   s = replaceBy Var Var x s
  renameValue (Lam x t) s = under Lam x renameTerm t s
  
  renameContext : Eq x => Context x a -> Subst x x -> Context x a
  renameContext (CoVal e) s  = CoVal $ renameCoValue e s
  renameContext (Mut x c) s  = under Mut x rename c s 
  
  renameCoValue : Eq x => CoValue x a -> Subst x x -> CoValue x a
  renameCoValue (CoVar a)      s = CoVar a
  renameCoValue (Fce f)        s = Fce $ renameForce f s
  renameCoValue (FLet x f tau) s = under2 FLet x renameForce f renameEnv tau s
  
  renameForce : Eq x => Force x a -> Subst x x -> Force x a
  renameForce (CoFree a) s = CoFree a
  renameForce (App t e)  s = App (renameTerm t s) (renameCoValue e s)
  
  renameEnv : Eq x => Environment x a -> Subst x x -> Environment x a
  renameEnv tau s = mapUntil (`matchBind` s) (`renameBind` s) tau
  
  renameBind : Eq x => Binding x a -> Subst x x -> Binding x a 
  renameBind (Bind x t)   s = Bind x (renameTerm t s)
  renameBind (CoBind a e) s = CoBind a (renameCoValue e s)

infix 4 ///
(///) : Eq x => Term x a -> Subst x x -> Term x a
(///) = renameTerm
