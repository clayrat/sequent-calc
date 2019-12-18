module LJ.LJQ

import Data.List
import Data.List.Quantifiers
import Subset
import Iter
import Lambda.STLC.Ty
import Lambda.STLC.Term
import Lambda.STLC.Smallstep
import LJ.LambdaC

%default total
%access public export

-- TODO add to Data.List.Quantifiers
indexAll : Elem x xs -> All p xs -> p x
indexAll  Here     (p::_  ) = p
indexAll (There e) ( _::ps) = indexAll e ps

mutual
  data Async : List Ty -> Ty -> Type where
    Foc : RSync g a -> Async g a                                     -- ~dereliction
    IL  : RSync g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c  -- generalized application
    HC  : RSync g a -> Async (a::g) b -> Async g b                   -- head cut, explicit substitution / letval
    MC  : Async g a -> Async (a::g) b -> Async g b                   -- mid cut, beta-redex

  -- cut-free RSyncs are values
  data RSync : List Ty -> Ty -> Type where
    Ax  : Elem a g -> RSync g a                     -- variable
    IR  : Async (a::g) b -> RSync g (a~>b)          -- lambda
    FHC : RSync g a -> RSync (a::g) b -> RSync g b  -- focused head cut
    -- no focused mid cut

mutual
  renameAsync : Subset g d -> Async g a -> Async d a
  renameAsync sub (Foc r)     = Foc $ renameRSync sub r
  renameAsync sub (IL r a el) = IL (renameRSync sub r) (renameAsync (ext sub) a) (sub el)
  renameAsync sub (HC r a)    = HC (renameRSync sub r) (renameAsync (ext sub) a)
  renameAsync sub (MC r l)    = MC (renameAsync sub r) (renameAsync (ext sub) l)

  renameRSync : Subset g d -> RSync g a -> RSync d a
  renameRSync sub (Ax el)   = Ax $ sub el
  renameRSync sub (IR a)    = IR (renameAsync (ext sub) a)
  renameRSync sub (FHC r l) = FHC (renameRSync sub r) (renameRSync (ext sub) l)

mutual
  renameMAsync : SubsetM g d -> Async g a -> Maybe (Async d a)
  renameMAsync subm (Foc r)     = Foc <$> renameMRSync subm r
  renameMAsync subm (IL r a el) = [| IL (renameMRSync subm r) (renameMAsync (extM subm) a) (subm el) |]
  renameMAsync subm (HC r a)    = [| HC (renameMRSync subm r) (renameMAsync (extM subm) a) |]
  renameMAsync subm (MC r l)    = [| MC (renameMAsync subm r) (renameMAsync (extM subm) l) |]

  renameMRSync : SubsetM g d -> RSync g a -> Maybe (RSync d a)
  renameMRSync subm (Ax el)   = Ax <$> subm el
  renameMRSync subm (IR a)    = IR <$> (renameMAsync (extM subm) a)
  renameMRSync subm (FHC r l) = [| FHC (renameMRSync subm r) (renameMRSync (extM subm) l) |]

shiftAsync : {auto is : IsSubset g d} -> Async g a -> Async d a
shiftAsync {is} = renameAsync (shift is)

shiftRSync : {auto is : IsSubset g d} -> RSync g a -> RSync d a
shiftRSync {is} = renameRSync (shift is)

mutual
  stepA : Async g a -> Maybe (Async g a)
  stepA (HC   (Ax el    )  t                 ) = Just $ renameAsync (contract el) t
  stepA (HC a@(IR _     ) (Foc p            )) = Just $ Foc $ FHC a p
  stepA (HC a@(IR u     ) (IL p t  Here     )) = Just $ MC (HC (FHC a p) u) (HC (shiftRSync a) (shiftAsync t))
  stepA (HC a@(IR _     ) (IL p t (There el))) = Just $ IL (FHC a p) (HC (shiftRSync a) (shiftAsync t)) el
  stepA (HC    k           m                 ) = [| HC (stepRS k) (pure m) |] <|> [| HC (pure k) (stepA m) |]

  stepA (MC   (Foc p    )  t                 ) = Just $ HC p t
  stepA (MC   (IL p v el)  t                 ) = Just $ IL p (MC v (shiftAsync t)) el
  stepA (MC    u           k                 ) = [| MC (stepA u) (pure k) |] <|> [| MC (pure u) (stepA k) |]
  stepA  _                                     = Nothing

  stepA (Foc p)                                = Foc <$> stepRS p

  stepRS : RSync g a -> Maybe (RSync g a)
  stepRS (FHC   (Ax el)  p             ) = Just $ renameRSync (contract el) p
  stepRS (FHC a@(IR _)  (Ax  Here     )) = Just a
  stepRS (FHC   (IR _)  (Ax (There el))) = Just $ Ax el
  stepRS (FHC a@(IR _)  (IR t         )) = Just $ IR $ HC (shiftRSync a) (shiftAsync t)
  stepRS (FHC    k       m             ) = [| FHC (stepRS k) (pure m) |] <|> [| FHC (pure k) (stepRS m) |]
  stepRS  _                              = Nothing

-- STLC embedding

mutual
  encodeVal : Val g a -> RSync g a
  encodeVal (Var e) = Ax e
  encodeVal (Lam t) = IR $ encodeTm t

  encodeTm : Tm g a -> Async g a
  encodeTm (V    v                        ) = Foc $ encodeVal v
  encodeTm (Let (App (V (Var e)) (V v)) p ) = IL (encodeVal v) (encodeTm p) e
  encodeTm (Let (App (V (Lam m)) (V v)) p ) = HC (IR $ encodeTm m) (IL (shiftRSync $ encodeVal v) (shiftAsync $ encodeTm p) Here)
  encodeTm (Let (App (V  v     )  n   ) p ) = assert_total $
                                              encodeTm $ Let n $ Let (App (V $ shiftVal v) (V $ Var Here)) (shiftTm p)
  encodeTm (Let (App  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let (App (V $ Var Here) (shiftTm n)) (shiftTm p)
  encodeTm (Let (Let  m           n   ) p ) = assert_total $
                                              encodeTm $ Let m $ Let n (shiftTm p)
  encodeTm (Let (V    v               ) p ) = HC (encodeVal v) (encodeTm p)
  encodeTm (App  m                      n ) = assert_total $
                                              encodeTm $ Let (App m n) (V $ Var Here)

isPseudoVal : Async g a -> Bool
isPseudoVal (Foc _)  = True
isPseudoVal (HC _ m) = isPseudoVal m
isPseudoVal  _       = False

isPseudoCoval : Async g a -> Bool
isPseudoCoval (IL p m el) = isJust (renameMAsync contractM m)
isPseudoCoval (HC p m)    = isPseudoCoval m
isPseudoCoval (MC m n)    = isPseudoCoval m && isJust (renameMAsync contractM n)
isPseudoCoval  _          = False

mutual
  forgetAsync : Async g a -> Term g a
  forgetAsync (Foc p)     = forgetRSync p
  forgetAsync (IL p m el) = App (Lam $ forgetAsync m) (App (Var el) (forgetRSync p))
  forgetAsync (HC p m)    = subst1 (forgetAsync m) (forgetRSync p)
  forgetAsync (MC n m)    = if isPseudoVal n && isPseudoCoval m
                              then subst1 (forgetAsync m) (forgetAsync n)
                              else App (Lam $ forgetAsync m) (forgetAsync n)

  forgetRSync : RSync g a -> Term g a
  forgetRSync (Ax el)   = Var el
  forgetRSync (IR n)    = Lam $ forgetAsync n
  forgetRSync (FHC p q) = subst1 (forgetRSync q) (forgetRSync p)

encode : Term g a -> Async g a
encode = encodeTm . embedLC

stepIter : Term [] a -> (Nat, Async [] a)
stepIter = iterCount stepA . encode

-- QJAM

mutual
  Env : List Ty -> Type
  Env = All Clos

  data Clos : Ty -> Type where
    Cl : RSync g a -> Env g -> Clos a

data Stack : Ty -> Ty -> Type where
  Mt : Stack a a
  Fun : Async (a::g) b -> Env g -> Stack b c -> Stack a c

data State : Ty -> Type where
  S1 : Async g a -> Env g -> Stack a b -> State b
  S2 : RSync g a -> Env g -> Async (a::d) b -> Env d -> Stack b c -> State c

initState : Async [] a -> State a
initState a = S1 a [] Mt

step : State b -> Maybe (State b)
step (S1 (Foc p)     e     (Fun t g c)) = Just $ S2 p e t g c
step (S1 (IL p t el) e              c ) = case indexAll el e of
                                            Cl (IR u) f => Just $ S2 p e u f (Fun t e c)
                                            _ => Nothing
step (S1 (HC p t)    e              c ) = Just $ S2 p e t e c
step (S2 (Ax el)     e t g          c ) = let Cl lu f = indexAll el e in
                                          Just $ S2 lu f t g c
step (S2 (IR u)      e t g          c ) = Just $ S1 t (Cl (IR u) e :: g) c
step  _                                 = Nothing

runQJAM : Term [] a -> (Nat, State a)
runQJAM = iterCount step . initState . encode

resultTm : Async [] (A~>A)
resultTm = Foc $ IR $ Foc $ Ax Here

testTm0 : Async [] (A~>A)
testTm0 = HC (IR $ Foc $ Ax Here) (IL (IR $ Foc $ Ax Here) (Foc $ Ax Here) Here)