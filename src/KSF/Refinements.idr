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

refinementARS : (Machine m, ARS x) => (m -> x -> Type) -> Type
refinementARS {m} {x} ref = 
  ( {a     : m} -> {b : x} -> ref a b -> reducible ARS_R b -> reducible ARS_R a
  , {a, a1 : m} -> {b : x} -> ref a b -> MRel {t=m} Tau  a a1 -> ref a1 b
  , {a, a1 : m} -> {b : x} -> ref a b -> MRel {t=m} Beta a a1 -> (b1 ** (ref a1 b1, ARS_R b b1))
  , {a     : m} -> {b : x} -> ref a b -> TerminatesOn (MRel Tau) a
  )

-- TODO correctness  

refinementM : (Machine m, Machine n) => (m -> n -> Type) -> Type
refinementM {m} {n} ref =
  ( {a     : m} -> {b : n} -> ref a b -> reducible ARS_R b -> reducible ARS_R a
  , {a, a1 : m} -> {b : n} -> ref a b -> MRel {t=m} Tau a a1 -> (b1 ** (ref a1 b1, MRel {t=n} Tau b b1)) 
  , {a, a1 : m} -> {b : n} -> ref a b -> MRel {t=m} Beta a a1 -> (b1 ** (ref a1 b1, MRel {t=n} Beta b b1))
  )  