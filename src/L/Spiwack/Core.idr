module L.Core

%access public export
%default total

mutual 
  data Cmd x = C (Term x) (Term x)

  data Term x = Var x | Mu x (Cmd x)

data Subst a b = Sub a b

infix 5 :=
(:=) : a -> b -> Subst a b
(:=) = Sub

mutual
  subst : Eq x => Cmd x -> Subst x (Term x) -> Cmd x
  subst (C t e) s = C (substTerm t s) (substTerm e s)
  
  substTerm : Eq x => Term x -> Subst x (Term x) -> Term x
  substTerm (Var x)  (Sub y m) = if (x == y) then m else Var x
  substTerm (Mu a c)  s        = Mu a (subst c s)

infix 3 //
(//) : Eq x => Cmd x -> Subst x (Term x) -> Cmd x
(//) = subst  
    
reduce : Eq x => Cmd x -> Cmd x
reduce (C (Var x1)   (Var x2  )) = (C (Var x1) (Var x2)) 
reduce (C (Mu a1 c1)  t        ) = c1 // a1 := t
reduce (C t          (Mu a2 c2)) = c2 // a2 := t

