module KSF.Refinements

import KSF.Prelim

%access public export
%default total

data Label = Tau | Beta

tbRel : Type -> Type
tbRel a = Label -> a -> a -> Type

any : (r : tbRel a) -> (x, y : a) -> Type
any r x y = (l ** r l x y)

interface Machine t where
  MRel : tbRel t

Machine t => ARS t where
  ARS_R = any MRel

refinementARS : (Machine a, ARS x) => (a -> x -> Type) -> Type
refinementARS {a} {x} ref = 
  ( {b : a} -> {y : x} -> ref b y -> reducible ARS_R y -> reducible ARS_R b
  , {b, b1 : a} -> {y : x} -> ref b y -> MRel {t=a} Tau  b b1 -> ref b1 y
  , {b, b1 : a} -> {y : x} -> ref b y -> MRel {t=a} Beta b b1 -> (y1 ** (ref b1 y1, ARS_R y y1))
  , {b : a} -> {y : x} -> ref b y -> TerminatesOn (MRel Tau) b
  )