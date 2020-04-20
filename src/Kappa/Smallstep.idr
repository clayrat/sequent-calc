module Kappa.Smallstep

import Data.List
import Subset
--import Iter
import Kappa.Term

%access public export
%default total

rename : Subset g d -> Term g a -> Term d a
rename r (Var  el)  = Var $ r el
rename r  Id        = Id
rename r  Bang      = Bang
rename r (Comp t u) = Comp (rename r t) (rename r u)
rename r (Lift t)   = Lift $ rename r t
rename r (Kap  t)   = Kap  (rename (ext r) t)

-- substitution

Subst : List (Ty,Ty) -> List (Ty,Ty) -> Type
Subst g d = {xy : (Ty,Ty)} -> Elem xy g -> Term d xy

exts : Subst g d -> Subst (xy::g) (xy::d)
exts _  Here      = Var Here
exts s (There el) = rename There (s el)

subst : Subst g d -> Term g a -> Term d a
subst s (Var  el)  = s el
subst s  Id        = Id
subst s  Bang      = Bang
subst s (Comp t u) = Comp (subst s t) (subst s u)
subst s (Lift t)   = Lift (subst s t)
subst s (Kap  t)   = Kap (subst (exts s) t)

subst1 : Term (a::g) b -> Term g a -> Term g b
subst1 {g} {a} t s = subst {g=a::g} go t
  where
  go : Subst (a::g) g
  go  Here      = s
  go (There el) = Var el
