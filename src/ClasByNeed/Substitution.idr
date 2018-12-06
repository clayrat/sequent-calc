module ClasByNeed.Substitution

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.Syntax

%access public export

data Subst a b = Sub a b

infix 5 :=
(:=) : a -> b -> Subst a b
(:=) = Sub

total
matchBind : Eq x => Binding x a -> Subst x b -> Bool 
matchBind (Bind x _ _) (Sub y _) = x == y

total
under : Eq a => (con : a -> c -> d) -> a -> (sub : c -> Subst a b -> c) -> c -> Subst a b -> d
under con x sub m s@(Sub y _) = 
  if (x == y) 
    then con x m
    else con x (sub m s)

total
under' : (Eq a, Alternative m, MonadState (List a) m) => 
         (con : a -> t -> b) -> a -> (sub : s -> Subst a c -> m t) -> (ren : t -> Subst a a -> s) -> t -> Subst a c -> m b
under' con x sub ren m s@(Sub y _) = 
  if (x == y) 
    then pure (con x m) 
    else do x' <- fresh
            con x' <$> sub (ren m (x := x')) s

total
under2 : Eq a => (con : a -> c -> d -> p) -> a -> (sub1 : c -> Subst a b -> c) -> c -> (sub2 : d -> Subst a b -> d) -> d -> Subst a b -> p                       
under2 con x sub1 m1 sub2 m2 s@(Sub y _) =
  if (x == y) 
    then con x m1 m2
    else con x (sub1 m1 s) (sub2 m2 s)

total
under2' : (Eq a, Alternative m, MonadState (List a) m) =>
          (con : a -> c -> d -> g) -> a 
       -> (sub1 : e -> Subst a b -> m c) -> (ren1 : c -> Subst a a -> e) -> c 
       -> (sub2 : f -> Subst a b -> m d) -> (ren2 : d -> Subst a a -> f) -> d 
       -> Subst a b -> m g                                         
under2' con x sub1 ren1 m1 sub2 ren2 m2 s@(Sub y _) =
  if (x == y) 
    then pure (con x m1 m2)
    else do x' <- fresh
            con x' <$> sub1 (ren1 m1 (x := x')) s <*> sub2 (ren2 m2 (x := x')) s

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

total
mapUntilM : Monad m => (a -> Bool) -> (a -> m a) -> List a -> m (List a)
mapUntilM p f []      = pure []
mapUntilM p f (x::xs) = 
  if p x 
    then (\x => x :: xs) <$> f x
    else List.(::) <$> f x <*> mapUntilM p f xs

mutual
  rename : Eq x => Command x a -> Subst x x -> Command x a 
  rename (C t e) s = C (renameTerm t s) (renameContext e s)
  
  renameTerm : Eq x => Term x a -> Subst x x -> Term x a
  renameTerm (Val v)  s = Val (renameValue v s)
  renameTerm (Mu a c) s = Mu a (rename c s)
  
  renameValue : Eq x => Value x a -> Subst x x -> Value x a
  renameValue (Var x)   s = replaceBy Var Var x s
  renameValue (Lam x t) s = under Lam x renameTerm t s
  
  renameContext : Eq x => Context x a -> Subst x x -> Context x a
  renameContext (CoVal e) s  = CoVal (renameCoValue e s)
  renameContext (Mut x c) s  = under Mut x rename c s 
  
  renameCoValue : Eq x => CoValue x a -> Subst x x -> CoValue x a
  renameCoValue (CoVar a)     s = CoVar a
  renameCoValue (Fce f)       s = Fce (renameForce f s)
  renameCoValue (FLet x f tau) s = under2 FLet x renameForce f renameEnv tau s
  
  renameForce : Eq x => Force x a -> Subst x x -> Force x a
  renameForce (CoFree a) s = CoFree a
  renameForce (App t e)  s = App (renameTerm t s) (renameCoValue e s)
  
  renameEnv : Eq x => Environment x a -> Subst x x -> Environment x a
  renameEnv tau s = mapUntil (\x => matchBind x s) (\x => renameBind x s) tau
  
  renameBind : Eq x => Binding x a -> Subst x x -> Binding x a 
  renameBind (Bind x a c) s = Bind x a (rename c s)

mutual
  subst : (Eq x, Alternative m, MonadState (List x) m) => 
          Command x a -> Subst x (Value x a) -> m (Command x a)
  subst (C t e) s = C <$> substTerm t s <*> substContext e s
  
  substTerm : (Eq x, Alternative m, MonadState (List x) m) => 
              Term x a -> Subst x (Value x a) -> m (Term x a)
  substTerm (Val v)  s = Val <$> substValue v s
  substTerm (Mu a c) s = Mu a <$> subst c s
  
  substValue : (Eq x, Alternative m, MonadState (List x) m) => 
               Value x a -> Subst x (Value x a) -> m (Value x a)
  substValue (Var x)   s = pure (replace Var x s)
  substValue (Lam x t) s = under' Lam x substTerm renameTerm t s
  
  substContext : (Eq x, Alternative m, MonadState (List x) m) => 
                 Context x a -> Subst x (Value x a) -> m (Context x a)
  substContext (CoVal e) s = CoVal <$> substCoValue e s
  substContext (Mut x c) s = under' Mut x subst rename c s
  
  substCoValue : (Eq x, Alternative m, MonadState (List x) m) => 
                 CoValue x a -> Subst x (Value x a) -> m (CoValue x a)
  substCoValue (CoVar a)     s = pure (CoVar a)
  substCoValue (Fce f)       s = Fce <$> substForce f s
  substCoValue (FLet x f tau) s =
    under2' FLet x substForce renameForce f substEnv renameEnv tau s
  
  substForce : (Eq x, Alternative m, MonadState (List x) m) => 
                 Force x a -> Subst x (Value x a) -> m (Force x a)
  substForce (CoFree a) s = pure (CoFree a)
  substForce (App t e)  s = App <$> substTerm t s <*> substCoValue e s
  
  substEnv : (Eq x, Alternative m, MonadState (List x) m) => 
             Environment x a -> Subst x (Value x a) -> m (Environment x a)
  substEnv tau s = mapUntilM (\x => matchBind x s) (\x => substBind x s) tau
  
  substBind : (Eq x, Alternative m, MonadState (List x) m) => 
              Binding x a -> Subst x (Value x a) -> m (Binding x a)
  substBind (Bind x a c) s = Bind x a <$> subst c s

mutual  
  corename : Eq a => Command x a -> Subst a a -> Command x a
  corename (C t e) s = C (corenameTerm t s) (corenameContext e s)
  
  corenameTerm : Eq a => Term x a -> Subst a a -> Term x a
  corenameTerm (Val v)  s = Val (corenameValue v s)
  corenameTerm (Mu a c) s = under Mu a corename c s
  
  corenameValue : Eq a => Value x a -> Subst a a -> Value x a
  corenameValue (Var x)   s = Var x
  corenameValue (Lam x t) s = Lam x (corenameTerm t s)
  
  corenameContext : Eq a => Context x a -> Subst a a -> Context x a
  corenameContext (CoVal e) s = CoVal (corenameCoValue e s)
  corenameContext (Mut x c) s = Mut x (corename c s)
  
  corenameCoValue : Eq a => CoValue x a -> Subst a a -> CoValue x a
  corenameCoValue (CoVar a)     s = replaceBy CoVar CoVar a s
  corenameCoValue (Fce f)       s = Fce (corenameForce f s)
  corenameCoValue (FLet x f tau) s =
    FLet x (corenameForce f s) (corenameEnv tau s)
  
  corenameForce : Eq a => Syntax.Force x a -> Subst a a -> Syntax.Force x a  
  corenameForce (CoFree a) s = CoFree a
  corenameForce (App t e)  s = App (corenameTerm t s) (corenameCoValue e s)
  
  corenameEnv : Eq a => Environment x a -> Subst a a -> Environment x a
  corenameEnv tau s = map (`corenameBind` s) tau
  
  corenameBind : Eq a => Binding x a -> Subst a a -> Binding x a
  corenameBind (Bind x a c) s = under (Bind x) a corename c s  

mutual
  cosubst : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Command a a -> Subst a (CoValue a a) -> Value a (Command a a)
  cosubst (C t e) s = C <$> cosubstTerm t s <*> cosubstContext e s
  
  cosubstTerm : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Term a a -> Subst a (CoValue a a) -> Value a (Term a a)
  cosubstTerm (Val v)  s = Val <$> cosubstValue v s
  cosubstTerm (Mu a c) s = under' Mu a cosubst corename c s
  
  cosubstValue : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Value a a -> Subst a (CoValue a a) -> Value a (Value a a)
  cosubstValue (Var x)   s = Var x
  cosubstValue (Lam x t) s = Lam x <$> cosubstTerm t s
  
  cosubstContext : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Context a a -> Subst a (CoValue a a) -> Value a (Context a a)
  cosubstContext (CoVal e) s = CoVal <$> cosubstCoValue e s
  cosubstContext (Mut x c) s = Mut x <$> cosubst c s
  
  cosubstCoValue : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => CoValue a a -> Subst a (CoValue a a) -> Value a (CoValue a a)
  cosubstCoValue (CoVar a)     s = pure (replace CoVar a s)
  cosubstCoValue (Fce f)       s = Fce <$> cosubstForce f s
  cosubstCoValue (FLet x f tau) s =
    FLet x <$> cosubstForce f s <*> cosubstEnv tau s
  
  cosubstForce : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Force a a -> Subst a (CoValue a a) -> Value a (Force a a)
  cosubstForce (CoFree a) s = pure (CoFree a)
  cosubstForce (App t e)  s = App <$> cosubstTerm t s <*> cosubstCoValue e s
  
  cosubstEnv : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Environment a a -> Subst a (CoValue a a) -> Value a (Environment a a)
  cosubstEnv tau s = mapUntilM (\x => matchBind x s) (\x => cosubstBind x s) tau
  
  cosubstBind : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Binding a a -> Subst a (CoValue a a) -> Value a (Binding a a)
  cosubstBind (Bind x a c) s = Bind x a <$> cosubst c s

infix 3 //
(//) : (Eq x, Alternative m, MonadState (List x) m) => Command x a -> Subst x (Value x a) -> m (Command x a)
(//) = subst

infix 3 //*
(//*) : (Eq a, Alternative (Value a), MonadState (List a) (Value a)) => Command a a -> Subst a (CoValue a a) -> Value a (Command a a)
(//*) = cosubst

infix 4 ///
(///) : Eq x => Term x a -> Subst x x -> Term x a
(///) = renameTerm