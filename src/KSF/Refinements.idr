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

composition : (Machine m, Machine n, ARS x) => 
              {r : m -> n -> Type} -> {s : n -> x -> Type} 
           -> refinementM r -> refinementARS s 
           -> refinementARS (\a, c => (b ** (r a b, s b c)))
composition {r} {s} (redab, tsimab, bsimab) (redbc, tsimbc, bsimbc, term) = 
  ( \(b ** (rab, sbc)), rac => 
      redab rab (redbc sbc rac)
  , \(b ** (rab, sbc)), mt => 
      let (b1**(ra1b1, mt2)) = tsimab rab mt in
      (b1**(ra1b1, tsimbc sbc mt2)) 
  , \(b ** (rab, sbc)), mb => 
      let 
        (b1**(ra1b1, mb2)) = bsimab rab mb 
        (c1**(sb1c1, abc)) = bsimbc sbc mb2 
       in 
      (c1**((b1**(ra1b1, sb1c1)), abc))
  , \(b ** (rab, sbc)) => 
      aux rab (term sbc)
  )
 where 
 aux : r a b -> TerminatesOn (MRel Tau) b -> TerminatesOn (MRel Tau) a
 aux rab1 (TerminatesC fb) = 
  TerminatesC $ \a1, raa1 => 
    let (b1**(ra1b1, mt1)) = tsimab rab1 raa1 in 
    aux ra1b1 (fb b1 mt1) 
