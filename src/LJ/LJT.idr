module LJ.LJT

import Data.List
import Data.List.Quantifiers
import Subset
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term

%default total
%access public export

-- TODO add to Data.List.Quantifiers
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps

mutual
  -- cut-free Asyncs are values
  data Async : List Ty -> Ty -> Type where
    Foc : Elem a g -> LSync g a b -> Async g b      -- contraction + variable
    IR  : Async (a::g) b -> Async g (a~>b)          -- lambda
    HC  : Async g a -> LSync g a b -> Async g b     -- head cut, beta-redex / generalized application
    MC  : Async g a -> Async (a::g) b -> Async g b  -- mid cut, term explicit substitution

  data LSync : List Ty -> Ty -> Ty -> Type where
    Ax  : LSync g a a                                   -- empty list
    IL  : Async g a -> LSync g b c -> LSync g (a~>b) c  -- prepending argument
    FHC : LSync g b a -> LSync g a c -> LSync g b c     -- focused head cut, concatenating contexts
    FMC : Async g a -> LSync (a::g) b c -> LSync g b c  -- focused mid cut, list explicit substitution

-- TODO for some reason totality checking takes a few minutes here without at least 2 asserts
mutual
  renameAsync : Subset g d -> Async g a -> Async d a
  renameAsync sub (Foc el k) = Foc (sub el) (renameLSync sub k)
  renameAsync sub (IR t)     = IR (renameAsync (ext sub) t)
  renameAsync sub (HC t c)   = HC (renameAsync sub t) (renameLSync sub c)
  renameAsync sub (MC t t2)  = assert_total $ MC (renameAsync sub t) (renameAsync (ext sub) t2)

  renameLSync : Subset g d -> LSync g a b -> LSync d a b
  renameLSync sub  Ax        = Ax
  renameLSync sub (IL t c)   = assert_total $ IL (renameAsync sub t) (renameLSync sub c)
  renameLSync sub (FHC c c2) = FHC (renameLSync sub c) (renameLSync sub c2)
  renameLSync sub (FMC t c)  = FMC (renameAsync sub t) (renameLSync (ext sub) c)

shiftAsync : {auto is : IsSubset g d} -> Async g a -> Async d a
shiftAsync {is} = renameAsync (shift is)

shiftLSync : {auto is : IsSubset g d} -> LSync g a b -> LSync d a b
shiftLSync {is} = renameLSync (shift is)

mutual
  stepA : Async g a -> Maybe (Async g a)
  stepA (HC (IR t)     (IL u k)          ) = Just $ HC (MC u t) k
  stepA (HC (IR t)      Ax               ) = Just $ IR t
  stepA (HC (Foc el k)  m                ) = Just $ Foc el (FHC k m)
--  stepA (HC (HC t k)    m                ) = Just $ HC t (FHC k m)
  stepA (HC  k          m                ) = [| HC (stepA k) (pure m) |] <|> [| HC (pure k) (stepLS m) |]

  stepA (MC  u         (IR t)            ) = Just $ IR $ MC (shiftAsync u) (shiftAsync t)
  stepA (MC  u         (Foc  Here      k)) = Just $ HC u (FMC u k)
  stepA (MC  u         (Foc (There el) k)) = Just $ Foc el (FMC u k)
--  stepA (MC  u         (HC k l)          ) = Just $ HC (MC u k) (FMC u l)
  stepA (MC  u          k                ) = [| MC (stepA u) (pure k) |] <|> [| MC (pure u) (stepA k) |]
  stepA  _                                 = Nothing

  stepLS : LSync g a b -> Maybe (LSync g a b)
  stepLS (FHC  Ax        m       ) = Just m
  stepLS (FHC (IL u k)   m       ) = Just $ IL u (FHC k m)
--  stepLS (FHC (FHC k l)  m       ) = Just $ FHC k (FHC l m)
  stepLS (FHC  k         m       ) = [| FHC (stepLS k) (pure m) |] <|> [| FHC (pure k) (stepLS m) |]

  stepLS (FMC  _         Ax      ) = Just Ax
  stepLS (FMC  u        (IL t k) ) = Just $ IL (MC u t) (FMC u k)
--  stepLS (FMC  u        (FHC k l)) = Just $ FHC (FMC u k) (FMC u l)
  stepLS (FMC  u         k       ) = [| FMC (stepA u) (pure k) |] <|> [| FMC (pure u) (stepLS k) |]
  stepLS  _                        = Nothing

-- STLC embedding

encode : Term g a -> Async g a
encode (Var e)    = Foc e Ax
encode (Lam t)    = IR $ encode t
encode (App t t2) = HC (encode t) (IL (encode t2) Ax)

stepIter : Term [] a -> (Nat, Async [] a)
stepIter = iterCount stepA . encode

-- TJAM

mutual
  Env : List Ty -> Type
  Env = All Clos

  data Clos : Ty -> Type where
    Cl : Async g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt  : Stack a a
  Arg : Clos a -> Stack b c -> Stack (a~>b) c

snoc : Stack a (b~>c) -> Clos b -> Stack a c
snoc  Mt         c = Arg c Mt
snoc (Arg c1 st) c = Arg c1 (snoc st c)

append : Stack a b -> Stack b c -> Stack a c
append  Mt        s2 = s2
append (Arg c s1) s2 = Arg c (append s1 s2)

data State : Ty -> Type where
  S1 : Async g a -> Env g -> Stack a b -> State b
  S2 : Async g a -> Env g -> Stack a x -> LSync d x y -> Env d -> Stack y b -> State b

initState : Async [] a -> State a
initState a = S1 a [] Mt

step : State b -> Maybe (State b)
step (S1 (IR t    ) e (Arg ug c)) = Just $ S1 t (ug::e) c
step (S1 (Foc el k) e         c ) = let Cl t g = indexAll el e in
                                    Just $ S2 t g Mt k e c
step (S1 (HC t   k) e         c ) = Just $ S2 t e Mt k e c
step (S2 t e b  Ax      _     c ) = Just $ S1 t e (append b c)
step (S2 t e b (IL u k) g     c ) = Just $ S2 t e (snoc b (Cl u g)) k g c
step  _                           = Nothing

runTJAM : Term [] a -> (Nat, State a)
runTJAM = iterCount step . initState . encode

-- tests

test1 : stepIter TestTm1 = (10, encode ResultTm)
test1 = Refl

test2 : stepIter TestTm2 = (10, encode ResultTm)
test2 = Refl

test3 : runTJAM TestTm1 = (12, initState $ encode ResultTm)
test3 = Refl

test4 : runTJAM TestTm2 = (12, initState $ encode ResultTm)
test4 = Refl
