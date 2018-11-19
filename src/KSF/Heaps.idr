module KSF.Heaps

import KSF.Prelim
import KSF.Programs
import KSF.Closures
import KSF.Codes

%access public export
%default total

interface Heap pa ha hp where
  get : hp -> ha -> Maybe (Maybe ((pa, ha), ha))
  put : hp -> (pa, ha) -> ha -> (hp, ha)
  HR1 : put h g a = (h1, b) -> get h1 b = Just (Just (g, a))
  HR2 : put h g a = (h1, b) -> Not (get h a = Nothing) -> get h a = get h1 a

data RepresentsEnv : (pa -> pa) -> (pa -> Maybe (Com pa)) -> (ha -> Maybe (Maybe ((pa, ha), ha))) -> ha -> List Clo -> Type where
  RENil  : {h : (ha -> Maybe (Maybe ((pa, ha), ha)))} -> {a : ha} -> {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
           h a = Just Nothing -> RepresentsEnv inc phi h a []
  RECons : {h : (ha -> Maybe (Maybe ((pa, ha), ha)))} -> {a : ha} -> {phi : pa -> Maybe (Com pa)} -> {inc : pa -> pa} -> 
           h a = Just (Just ((q,b),c)) -> RepresentsPro inc phi q p -> RepresentsEnv inc phi h b f -> RepresentsEnv inc phi h c e -> RepresentsEnv inc phi h a (ClosC p f :: e)

Heap Nat Nat (List ((Nat, Nat), Nat)) where
  put h g a = (h ++ [(g,a)], S (length h))
  get h  Z    = Just Nothing
  get h (S a) with (index' a h)
    | Just (g, b) = Just (Just (g, b))
    | Nothing = Nothing
  HR1 Refl {h} {g} {a} = rewrite indexMid {as=h} {b=(g,a)} {cs=[]} in Refl
  HR2 Refl c     {a=Z}   = Refl
  HR2 Refl c {h} {g} {a=S a} with (index' a h) proof ix
    | Just (j,b) = 
      rewrite indexAppend {x=a} {l=h} {y=(j,b)} {m=[(g, S a)]} (sym ix) in
      Refl
    | Nothing = absurd $ c Refl

representsEnvFunctional : (Code c pa, Heap pa ha hp) => functional (RepresentsEnv inc phi h)              
representsEnvFunctional                             x []               []                  (RENil prf)                          (RENil prf1)                                      = Refl
representsEnvFunctional                             x []               (ClosC p1 f1 :: e1) (RENil prf)                          (RECons prf1 rpq1 ref1 ree1)                      = 
  absurd $ justInjective $ trans (sym prf) prf1
representsEnvFunctional                             x (ClosC p f :: e) []                  (RECons prf rpq ref ree)             (RENil prf1)                                      = 
  absurd $ justInjective $ trans (sym prf1) prf
representsEnvFunctional @{cd} @{he} {inc} {phi} {h} x (ClosC p f :: e) (ClosC p1 f1 :: e1) (RECons {q} {b} {c} prf rpq ref ree) (RECons {q=q1} {b=b1} {c=c1} prf1 rpq1 ref1 ree1) = 
  let Refl = justInjective $ justInjective $ trans (sym prf1) prf in
  rewrite representsProFunctional @{cd} q p p1 rpq rpq1 in
  rewrite representsEnvFunctional @{cd} @{he} {inc} {phi} {h} b f f1 ref ref1 in
  cong $ representsEnvFunctional @{cd} @{he} {inc} {phi} {h} c e e1 ree ree1

representsEnvExtend : (hi : Heap pa ha hp) => 
                      ({x : ha} -> Not (get @{hi} h x = Nothing) -> get @{hi} h x = get @{hi} h1 x) 
                   -> RepresentsEnv inc phi (get @{hi} h) a e 
                   -> RepresentsEnv inc phi (get @{hi} h1) a e
representsEnvExtend {a} ext (RENil prf)              = RENil $ rewrite sym $ ext {x=a} (notNothingIsJust prf) in prf
representsEnvExtend {a} {h} {h1} ext (RECons {q} {b} {c} prf rpq ref ree) = 
  RECons {q}
    (rewrite sym $ ext {x=a} (notNothingIsJust prf) in prf)
    rpq
    (representsEnvExtend {a=b} {h} {h1} ext ref)
    (representsEnvExtend {a=c} {h} {h1} ext ree)
