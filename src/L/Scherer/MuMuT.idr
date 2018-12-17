module L.Scherer.MuMuT

import Data.List
import L.Scherer.Subset

%access public export
%default total

data Ty = A 
        | Imp Ty Ty | Ten  Ty Ty | One  --| Bot
        | Sum Ty Ty | With Ty Ty | Zero --| Top

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C : Term g a d -> CoTerm g a d -> Cmd g d

  data Term : List Ty -> Ty -> List Ty -> Type where
    Var  : Elem a g -> Term g a d
    Mu   : Cmd g (a::d) -> Term g a d
    MatC : Cmd (a::g) (b::d) -> Term g (Imp a b) d
    Pair : Term g a d -> Term g b d -> Term g (Ten a b) d
    Triv : Term g One d
    Inl  : Term g a d -> Term g (Sum a b) d
    Inr  : Term g b d -> Term g (Sum a b) d
    MatR : Cmd g (a::d) -> Cmd g (b::d) -> Term g (With a b) d

  data CoTerm : List Ty -> Ty -> List Ty -> Type where
    CoVar : Elem a d -> CoTerm g a d
    Mut   : Cmd (a::g) d -> CoTerm g a d
    AppC  : Term g a d -> CoTerm g b d -> CoTerm g (Imp a b) d
    MatP  : Cmd (a::b::g) d -> CoTerm g (Ten a b) d
    Empty : CoTerm g Zero d
    MatS  : Cmd (a::g) d -> Cmd (b::g) d -> CoTerm g (Sum a b) d
    Prjl  : CoTerm g a d -> CoTerm g (With a b) d
    Prjr  : CoTerm g b d -> CoTerm g (With a b) d

mutual    
  shiftCmd : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Cmd g d -> Cmd g1 d1    
  shiftCmd (C t e) = C (shiftTerm t) (shiftCoTerm e)

  shiftTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> Term g a d -> Term g1 a d1    
  shiftTerm {is1}       (Var el)     = Var $ shift is1 el
  shiftTerm       {is2} (Mu c)       = Mu $ shiftCmd {is2=Cons2 is2} c
  shiftTerm {is1} {is2} (MatC c)     = MatC $ shiftCmd {is1=Cons2 is1} {is2=Cons2 is2} c
  shiftTerm             (Pair t u)   = Pair (shiftTerm t) (shiftTerm u)
  shiftTerm              Triv        = Triv
  shiftTerm             (Inl t1)     = Inl $ shiftTerm t1
  shiftTerm             (Inr t2)     = Inr $ shiftTerm t2
  shiftTerm             (MatR c1 c2) = MatR (shiftCmd c1) (shiftCmd c2)

  shiftCoTerm : {auto is1 : IsSubset g g1} -> {auto is2 : IsSubset d d1} -> CoTerm g a d -> CoTerm g1 a d1    
  shiftCoTerm       {is2} (CoVar el)   = CoVar $ shift is2 el
  shiftCoTerm {is1}       (Mut c)      = Mut $ shiftCmd {is1=Cons2 is1} c
  shiftCoTerm             (AppC t e)   = AppC (shiftTerm t) (shiftCoTerm e)
  shiftCoTerm             (MatP c)     = MatP $ shiftCmd c
  shiftCoTerm              Empty       = Empty
  shiftCoTerm             (MatS c1 c2) = MatS (shiftCmd c1) (shiftCmd c2)
  shiftCoTerm             (Prjl e1)    = Prjl $ shiftCoTerm e1
  shiftCoTerm             (Prjr e2)    = Prjr $ shiftCoTerm e2

let_ : Term g a d -> Term (a::g) b d -> Term g b d    
let_ e0 e1 = Mu $ C (shiftTerm e0) 
                    (Mut $ C (shiftTerm e1) (CoVar Here))

let2 : Term g (Ten a b) d -> Term (a::b::g) c d -> Term g c d  
let2 t u = Mu $ C (shiftTerm t) 
                  (MatP $ C (shiftTerm u) (CoVar Here)) 

lam : Term (a::g) b d -> Term g (Imp a b) d
lam t = 
  MatC $ C (shiftTerm t) (CoVar Here)

app : Term g (Imp a b) d -> Term g a d -> Term g b d
app t u = 
  Mu $ 
  C (shiftTerm t) (AppC (shiftTerm u) (CoVar Here))

callcc : Term g (Imp (Imp a b) a) (a::d) -> Term g a d
callcc f = 
  Mu $ C f
         (AppC 
           (MatC $ C (Var Here) (CoVar $ There Here))
           (CoVar Here))

-- 
llv0 : Term [] (Imp A (Imp A A)) []      
llv0 = lam $ lam $ Var Here

llv1 : Term [] (Imp A (Imp A A)) []      
llv1 = lam $ lam $ Var $ There Here

mutual
  subst : Cmd (a::g) d -> Term g a d -> Cmd g d
  subst (C t e) tm = C (assert_total $ substTerm t tm) (assert_total $ substCoTerm e tm)

  substTerm : Term (a::g) c d -> Term g a d -> Term g c d
  substTerm (Var Here)       tm = tm
  substTerm (Var (There el)) _  = Var el
  substTerm (Mu cmd)         tm = Mu $ subst (shiftCmd cmd) (shiftTerm tm)
  substTerm (MatC cmd)       tm = MatC $ subst (shiftCmd cmd) (shiftTerm tm)
  substTerm (Pair t u)       tm = Pair (substTerm t tm) (substTerm u tm)
  substTerm  Triv            _  = Triv
  substTerm (Inl t1)         tm = Inl $ substTerm t1 tm
  substTerm (Inr t2)         tm = Inr $ substTerm t2 tm
  substTerm (MatR c1 c2)     tm = MatR (subst (shiftCmd c1) (shiftTerm tm)) (subst (shiftCmd c2) (shiftTerm tm))

  substCoTerm : CoTerm (a::g) c d -> Term g a d -> CoTerm g c d
  substCoTerm (CoVar el)   tm = CoVar el
  substCoTerm (Mut cmd)    tm = Mut $ subst (shiftCmd cmd) (shiftTerm tm) 
  substCoTerm (AppC t e)   tm = AppC (substTerm t tm) (substCoTerm e tm)
  substCoTerm (MatP cmd)   tm = MatP $ subst (shiftCmd cmd) (shiftTerm tm) 
  substCoTerm  Empty       _  = Empty
  substCoTerm (MatS c1 c2) tm = MatS (subst (shiftCmd c1) (shiftTerm tm)) (subst (shiftCmd c2) (shiftTerm tm))
  substCoTerm (Prjl e1)    tm = Prjl $ substCoTerm e1 tm
  substCoTerm (Prjr e2)    tm = Prjr $ substCoTerm e2 tm

mutual
  cosubst : Cmd g (a::d) -> CoTerm g a d -> Cmd g d
  cosubst (C t e) ct = C (assert_total $ cosubstTerm t ct) (assert_total $ cosubstCoTerm e ct)

  cosubstTerm : Term g c (a::d) -> CoTerm g a d -> Term g c d
  cosubstTerm (Var el)     _  = Var el
  cosubstTerm (Mu cmd)     ct = Mu $ cosubst (shiftCmd cmd) (shiftCoTerm ct)
  cosubstTerm (MatC cmd)   ct = MatC $ cosubst (shiftCmd cmd) (shiftCoTerm ct)
  cosubstTerm (Pair t u)   ct = Pair (cosubstTerm t ct) (cosubstTerm u ct)
  cosubstTerm  Triv        _  = Triv
  cosubstTerm (Inl t1)     ct = Inl $ cosubstTerm t1 ct
  cosubstTerm (Inr t2)     ct = Inr $ cosubstTerm t2 ct
  cosubstTerm (MatR c1 c2) ct = MatR (cosubst (shiftCmd c1) (shiftCoTerm ct)) (cosubst (shiftCmd c2) (shiftCoTerm ct))

  cosubstCoTerm : CoTerm g c (a::d) -> CoTerm g a d -> CoTerm g c d
  cosubstCoTerm (CoVar Here)       ct = ct
  cosubstCoTerm (CoVar (There el)) _  = CoVar el
  cosubstCoTerm (Mut cmd)          ct = Mut $ cosubst cmd (shiftCoTerm ct)
  cosubstCoTerm (AppC t e)         ct = AppC (cosubstTerm t ct) (cosubstCoTerm e ct)
  cosubstCoTerm (MatP cmd)         ct = MatP $ cosubst cmd (shiftCoTerm ct)
  cosubstCoTerm  Empty             _  = Empty
  cosubstCoTerm (MatS c1 c2)       ct = MatS (cosubst c1 (shiftCoTerm ct)) (cosubst c2 (shiftCoTerm ct))
  cosubstCoTerm (Prjl e1)          ct = Prjl $ cosubstCoTerm e1 ct
  cosubstCoTerm (Prjr e2)          ct = Prjr $ cosubstCoTerm e2 ct

{-  
reduce : Cmd g d -> Maybe (Cmd g d)
reduce (C (Mu c)       e          ) = Just $ cosubst c e
reduce (C  t          (Mut c)     ) = Just $ subst c t
reduce (C (MatC c)    (AppC t e)  ) = Just $ subst (cosubst c (shiftCoTerm e)) (shiftTerm t)
reduce (C (Pair t u)  (MatP c)    ) = Just $ subst (subst c (shiftTerm t)) u
reduce (C (Inl t1)    (MatS c1 _) ) = Just $ subst c1 t1
reduce (C (Inr t2)    (MatS _ c2) ) = Just $ subst c2 t2
reduce (C (MatR c1 _) (Prjl e1)   ) = Just $ cosubst c1 e1
reduce (C (MatR _ c2) (Prjr e2)   ) = Just $ cosubst c2 e2
reduce  _                           = Nothing

reduceIter : Cmd g d -> Maybe (Cmd g d)
reduceIter c with (reduce c)
  | Nothing = Just c
  | Just c' = assert_total $ reduceIter c'
-}