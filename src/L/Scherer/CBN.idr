module L.Scherer.CBN

import Data.List
import L.Scherer.Subset

%access public export
%default total
%hide Language.Reflection.Var

data Ty = A | Imp Ty Ty | Ten Ty Ty

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    MatC : Cmd (a::g) (b::d) -> Term g (Imp a b) d
    Pair : Term g a d -> Term g b d -> Term g (Ten a b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVal : CoValue g a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d

  data CoValue : List Ty -> Ty -> List Ty -> Type where    
    CoVar : Elem a d -> CoValue g a d
    AppC  : Term g a d -> CoValue g b d -> CoValue g (Imp a b) d
    MatP  : Cmd (a::b::g) d -> CoValue g (Ten a b) d

mutual    
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1    
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1    
  shiftTerm {is1}       (Var el)   = Var $ shift is1 el
  shiftTerm       {is2} (Mu c)     = Mu $ shiftCmd {is2=Cons2 is2} c
  shiftTerm {is1} {is2} (MatC c)   = MatC $ shiftCmd {is1=Cons2 is1} {is2=Cons2 is2} c
  shiftTerm             (Pair t u) = Pair (shiftTerm t) (shiftTerm u)

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm       (CoVal cv) = CoVal $ shiftCoValue cv
  shiftCoTerm {is1} (Mut c)   = Mut $ shiftCmd {is1=Cons2 is1} c

  shiftCoValue : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoValue g a d -> CoValue g1 a d1    
  shiftCoValue {is2} (CoVar el) = CoVar $ shift is2 el
  shiftCoValue       (AppC t e) = AppC (shiftTerm t) (shiftCoValue e)
  shiftCoValue       (MatP c)   = MatP $ shiftCmd c

mutual
  subst : Cmd (a::g) d -> Term g a d -> Cmd g d
  subst (C t e) va = C (assert_total $ substTerm t va) (assert_total $ substCoTerm e va)

  substTerm : Term (a::g) c d -> Term g a d -> Term g c d
  substTerm (Var  Here)      va = va
  substTerm (Var (There el)) _  = Var el
  substTerm (Mu cmd)         va = Mu $ subst (shiftCmd cmd) (shiftTerm va)
  substTerm (MatC cmd)       va = MatC $ subst (shiftCmd cmd) (shiftTerm va)
  substTerm (Pair t u)       va = Pair (substTerm t va) (substTerm u va)

  substCoTerm : CoTerm (a::g) c d -> Term g a d -> CoTerm g c d
  substCoTerm (CoVal v) va = CoVal $ substCoValue v va
  substCoTerm (Mut cmd) va = Mut $ subst (shiftCmd cmd) (shiftTerm va) 

  substCoValue : CoValue (a::g) c d -> Term g a d -> CoValue g c d
  substCoValue (CoVar el) va = CoVar el
  substCoValue (AppC t e) va = AppC (substTerm t va) (substCoValue e va)
  substCoValue (MatP cmd) va = MatP $ subst (shiftCmd cmd) (shiftTerm va) 

mutual
  cosubst : Cmd g (a::d) -> CoValue g a d -> Cmd g d
  cosubst (C t e) ct = C (assert_total $ cosubstTerm t ct) (assert_total $ cosubstCoTerm e ct)

  cosubstTerm : Term g c (a::d) -> CoValue g a d -> Term g c d
  cosubstTerm (Var el)   _  = Var el
  cosubstTerm (Mu cmd)   ct = Mu $ cosubst (shiftCmd cmd) (shiftCoValue ct)
  cosubstTerm (MatC cmd) ct = MatC $ cosubst (shiftCmd cmd) (shiftCoValue ct)
  cosubstTerm (Pair t u) ct = Pair (cosubstTerm t ct) (cosubstTerm u ct)

  cosubstCoTerm : CoTerm g c (a::d) -> CoValue g a d -> CoTerm g c d
  cosubstCoTerm (CoVal cv)  ct = CoVal $ cosubstCoValue cv ct
  cosubstCoTerm (Mut cmd)   ct = Mut $ cosubst cmd (shiftCoValue ct)

  cosubstCoValue : CoValue g c (a::d) -> CoValue g a d -> CoValue g c d
  cosubstCoValue (CoVar Here)       ct = ct
  cosubstCoValue (CoVar (There el)) _  = CoVar el
  cosubstCoValue (AppC t e)         ct = AppC (cosubstTerm t ct) (cosubstCoValue e ct)
  cosubstCoValue (MatP cmd)         ct = MatP $ cosubst cmd (shiftCoValue ct)

reduce : Cmd g d -> Maybe (Cmd g d)
reduce (C  t         (Mut c)            ) = Just $ subst c t
reduce (C (Mu c)     (CoVal cv)         ) = Just $ cosubst c cv
reduce (C (MatC c)   (CoVal (AppC t cv))) = Just $ cosubst (subst c (shiftTerm t)) (shiftCoValue cv)
reduce (C (Pair t u) (CoVal (MatP c))   ) = Just $ subst (subst c (shiftTerm t)) u
reduce  _                                 = Nothing

reduceIter : Cmd g d -> Maybe (Cmd g d)
reduceIter c with (reduce c)
  | Nothing = Just c
  | Just c' = assert_total $ reduceIter c'
