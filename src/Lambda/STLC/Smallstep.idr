module Lambda.STLC.Smallstep

import Data.List
import Subset
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

-- partially following http://r6.ca/blog/20171008T222703Z.html

-- aka weaken, map operation for the functor `\g => Term g a`
rename : Subset g d -> Term g a -> Term d a
rename r (Var el)    = Var $ r el
rename r (Lam t)     = Lam $ rename (ext r) t
rename r (App t1 t2) = App (rename r t1) (rename r t2)

-- aka module:
--  * a block of terms for simultaneous substitution
--  * a list of terms of types D all in the same context G
--  * an arrow in a category of contexts (a profunctor)
Subst : List Ty -> List Ty -> Type
Subst g d = {x : Ty} -> Elem x d -> Term g x

-- identity arrow in the category of contexts
Sid : Subst g g
Sid = Var

Sempty : Subst g []
Sempty = absurd

SCons : Term g a -> Subst g d -> Subst g (a::d)
SCons t s  Here      = t
SCons t s (There el) = s el

Slmap : Subset g1 g2 -> Subst g1 d -> Subst g2 d
Slmap f s = rename f . s

-- not only does filtering, but also duplication (and permutations)
Srmap : Subset d1 d2 -> Subst g d2 -> Subst g d1
Srmap g s = s . g

Sweak : Subst g d -> Subst (a::g) d
Sweak = Slmap There

exts : Subst g d -> Subst (b::g) (b::d)
exts s = SCons (Var Here) (Sweak s)

-- simultaneous substutition of all free variables of a Term with the terms from a module
subst : Subst g d -> Term d a -> Term g a
subst s (Var el)    = s el
subst s (Lam t)     = Lam $ subst (exts s) t
subst s (App t1 t2) = App (subst s t1) (subst s t2)

-- arrow composition in the category of contexts
Scompose : Subst g d -> Subst d k -> Subst g k
Scompose s1 s2 = subst s1 . s2

-- instantiation of the last free variable of a term
subst1 : Term (a::g) b -> Term g a -> Term g b
subst1 t s = subst (SCons s Sid) t

step : Term g a -> Maybe (Term g a)
step (App (Lam body) sub) = Just $ subst1 body sub
step (App  t1        t2 ) =
  if isVal t1
    then Nothing
    else [| App (step t1) (pure t2) |]
step  _ = Nothing

stepIter : Term g a -> Term g a
stepIter = iter step
