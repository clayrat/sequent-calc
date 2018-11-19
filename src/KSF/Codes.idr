module KSF.Codes

import KSF.Prelim
import KSF.Programs

%access public export
%default total

data Com : Type -> Type where
  RetC :        Com pa
  VarC : Nat -> Com pa
  AppC :        Com pa
  LamC : pa ->  Com pa

Uninhabited (RetC = VarC _) where
  uninhabited Refl impossible

Uninhabited (RetC = AppC) where
  uninhabited Refl impossible

Uninhabited (RetC = LamC _) where
  uninhabited Refl impossible

Uninhabited (AppC = VarC _) where
  uninhabited Refl impossible  

Uninhabited (AppC = LamC _) where
  uninhabited Refl impossible  
  
Uninhabited (LamC _ = VarC _) where
  uninhabited Refl impossible  

varCInjective : VarC a = VarC b -> a = b  
varCInjective Refl = Refl

lamCInjective : LamC a = LamC b -> a = b  
lamCInjective Refl = Refl

interface Code c pa where  
  phi : c -> pa -> Maybe (Com pa)
  inc : pa -> pa

phiNat : List (Com Nat) -> Nat -> Maybe (Com Nat)
phiNat c p with (index' p c)
  | Just  RetC    = Just RetC
  | Just (VarC n) = Just (VarC n)
  | Just  AppC    = Just AppC
  | Just (LamC k) = Just (LamC (p+k))
  | Nothing       = Nothing

Code (List (Com Nat)) Nat where
  phi = phiNat
  inc = S
  
data RepresentsPro : (pa -> pa) -> (pa -> Maybe (Com pa)) -> pa -> Pro -> Type where
  RPRet : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
          phi p = Just RetC                                                                     -> RepresentsPro inc phi p  RetT
  RPVar : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
          phi p = Just (VarC x) -> RepresentsPro inc phi (inc p) r                              -> RepresentsPro inc phi p (VarT x r)
  RPLam : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
          phi p = Just (LamC q) -> RepresentsPro inc phi (inc p) r -> RepresentsPro inc phi q s -> RepresentsPro inc phi p (LamT s r)
  RPApp : {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
          phi p = Just AppC     -> RepresentsPro inc phi (inc p) r                              -> RepresentsPro inc phi p (AppT r)

representsProFunctional : Code c pa => functional (RepresentsPro inc phi)          
representsProFunctional       _  RetT       RetT        (RPRet prf)                         (RPRet prf1)                               = Refl
representsProFunctional       _  RetT      (VarT _ _)   (RPRet prf)                         (RPVar prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional       _  RetT      (LamT _ _)   (RPRet prf)                         (RPLam prf1 _ _)                           = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional       _  RetT      (AppT _)     (RPRet prf)                         (RPApp prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional       _ (VarT _ _)  RetT        (RPVar prf _)                       (RPRet prf1)                               = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional @{cd} x (VarT k r) (VarT k1 r1) (RPVar {inc} prf rpr)               (RPVar {inc} prf1 rpr1)                    = 
  rewrite varCInjective $ justInjective $ trans (sym prf1) prf in 
  cong $ representsProFunctional @{cd} (inc x) r r1 rpr rpr1
representsProFunctional       _ (VarT _ _) (LamT _  _)  (RPVar prf _)                       (RPLam prf1 _ _)                           = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional       _ (VarT _ _) (AppT _)     (RPVar prf _)                       (RPApp prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional       _ (LamT _ _)  RetT        (RPLam prf _ _)                     (RPRet prf1)                               = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional       _ (LamT _ _) (VarT _ _)   (RPLam prf _ _)                     (RPVar prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional @{cd} x (LamT s r) (LamT s1 r1) (RPLam {inc} {phi} {q} prf rpr rpq) (RPLam {inc} {phi} {q=q1} prf1 rpr1 rpq1)  = 
  let 
    qq1 = lamCInjective $ justInjective $ trans (sym prf1) prf 
    rpq2 = replace {P=\z=>RepresentsPro inc phi z s1} qq1 rpq1 
   in  
  rewrite representsProFunctional @{cd} q s s1 rpq rpq2 in
  cong $ representsProFunctional @{cd} (inc x) r r1 rpr rpr1
representsProFunctional       _ (LamT _ _) (AppT _)     (RPLam prf _ _)                     (RPApp prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional       _ (AppT _)    RetT        (RPApp prf _)                       (RPRet prf1)                               = 
  absurd $ justInjective $ trans (sym prf1) prf
representsProFunctional       _ (AppT _)   (VarT _ _)   (RPApp prf _)                       (RPVar prf1 _)                             = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional       _ (AppT _)   (LamT _ _)   (RPApp prf _)                       (RPLam prf1 _ _)                           = 
  absurd $ justInjective $ trans (sym prf) prf1
representsProFunctional @{cd} x (AppT r)   (AppT r1)    (RPApp {inc} prf rpr)               (RPApp {inc} prf1 rpr1)                    = 
  cong $ representsProFunctional @{cd} (inc x) r r1 rpr rpr1

fetch : Pro -> List (Com Nat)
fetch  RetT      = [RetC]
fetch (AppT p)   = AppC :: fetch p
fetch (VarT x p) = VarC x :: fetch p
fetch (LamT q p) = 
  let cP = fetch p in
  LamC (1 + length cP) :: cP ++ fetch q

fetchCorrect' : RepresentsPro S (phiNat (c1 ++ fetch p ++ c2)) (length c1) p
fetchCorrect' {c1} {c2} {p=RetT}     = 
  RPRet $ 
    rewrite indexMid {as=c1} {b=RetC} {cs=c2} in Refl
fetchCorrect' {c1} {c2} {p=VarT k x} = 
  RPVar 
    (rewrite indexMid {as=c1} {b=VarC k} {cs=fetch x ++ c2} in Refl) 
    (rewrite consMid {as=c1} {b=VarC k} {bs=fetch x} {cs=c2} in 
     rewrite sym $ lenPost {as=c1} {b=VarC k} in 
     fetchCorrect' {c1=c1++[VarC k]} {p=x} {c2})
fetchCorrect' {c1} {c2} {p=AppT x}   = 
  RPApp
    (rewrite indexMid {as=c1} {b=AppC} {cs=fetch x ++ c2} in Refl) 
    (rewrite consMid {as=c1} {b=AppC} {bs=fetch x} {cs=c2} in 
     rewrite sym $ lenPost {as=c1} {b=AppC} in 
     fetchCorrect' {c1=c1++[AppC]} {p=x} {c2})
fetchCorrect' {c1} {c2} {p=LamT x y} = 
  RPLam
    {q = length c1 + S (length (fetch y))}
    (rewrite indexMid {as=c1} {b=LamC (S (length (fetch y)))} {cs=(fetch y ++ fetch x) ++ c2} in Refl)
    (rewrite sym $ appendAssociative (fetch y) (fetch x) c2 in
     rewrite consMid {as=c1} {b=LamC (S (length (fetch y)))} {bs=fetch y} {cs=fetch x ++ c2} in  
     rewrite sym $ lenPost {as=c1} {b=LamC (S (length (fetch y)))} in  
     fetchCorrect' {c1=c1++[LamC (S (length (fetch y)))]} {p=y} {c2=fetch x ++ c2})
    (rewrite sym $ appendAssociative (fetch y) (fetch x) c2 in
     rewrite appendAssociative c1 (LamC (S (length (fetch y))) :: fetch y) (fetch x ++ c2) in
     rewrite sym $ lengthAppend c1 (LamC (S (length (fetch y))) :: fetch y) in
     fetchCorrect' {c1=c1++LamC (S (length (fetch y))) :: fetch y} {p=x} {c2})

fetchCorrect : RepresentsPro S (phiNat (fetch p)) 0 p
fetchCorrect {p} = 
  rewrite sym $ appendNilRightNeutral (fetch p) in 
  fetchCorrect' {c1=[]} {c2=[]} {p}
