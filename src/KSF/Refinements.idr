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