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
    HC  : RSync g a -> Async (a::g) b -> Async g b                   -- head cut, letval
    MC  : Async g a -> Async (a::g) b -> Async g b                   -- mid cut, explicit substitution/beta-redex

  -- cut-free RSyncs are values
  data RSync : List Ty -> Ty -> Type where
    Ax  : Elem a g -> RSync g a                     -- variable
    IR  : Async (a::g) b -> RSync g (a~>b)          -- lambda
    FHC : RSync g a -> RSync (a::g) b -> RSync g b  -- focused head cut, explicit substitution
    -- no focused mid cut

-- structural rules

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

-- terms from paper

lem1 : Async ((a~>b)::a::g) b
lem1 = IL (Ax $ There Here) (Foc $ Ax Here) Here

cut4 : Async g a -> RSync (a::g) b -> Async g b
cut4 n = MC n . Foc

cut5 : RSync g a -> RSync (a::g) b -> Async g b
cut5 p q = Foc $ FHC p q

IRA : Async (a::g) b -> Async g (a~>b)
IRA = Foc . IR

ILA : Async g a -> Async (b::g) c -> Elem (a~>b) g -> Async g c
ILA n m el = MC n $ MC (IL (Ax Here) (Foc $ Ax Here) (There el)) (shiftAsync m)

-- reduction

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

-- strong reduction

isCoval : Async g a -> Bool
isCoval (Foc (Ax Here)) = True
isCoval (IL p m Here)   = isJust (renameMRSync contractM p) && isJust (renameMAsync contractM (renameAsync permute m))
isCoval  _              = False

mutual
  stepStrA : Async g a -> Maybe (Async g a)

  stepStrA (HC p (Foc q)            ) = Just $ Foc $ FHC p q
  stepStrA (HC p (IL q m  Here)     ) = Just $ MC (Foc p) (IL (FHC (shiftRSync p) (shiftRSync q))
                                                              (HC (shiftRSync p) (shiftAsync m)) Here)
  stepStrA (HC p (IL q m (There el))) = Just $ IL (FHC p q) (HC (shiftRSync p) (shiftAsync m)) el
  stepStrA (HC p (MC n m)           ) = Just $ MC (HC p n) (HC (shiftRSync p) (shiftAsync m))
  stepStrA (HC p  m                 ) = [| HC (stepStrRS p) (pure m) |] <|> [| HC (pure p) (stepStrA m) |]

  stepStrA (MC (Foc (IR n))              (IL p m Here)) = do p' <- renameMRSync contractM p
                                                             m' <- renameMAsync contractM (renameAsync permute m)
                                                             pure $ MC (MC (Foc p') n) m'
  stepStrA (MC (Foc (Ax el))              m           ) = Just $ renameAsync (contract el) m
  stepStrA (MC (IL p n el)                m           ) = Just $ IL p (MC n (shiftAsync m)) el
  stepStrA (MC (MC (Foc p) (IL q n Here)) m           ) =
    do q' <- renameMRSync contractM q
       n' <- renameMAsync contractM (renameAsync permute n)
       pure $ MC (Foc p) (IL (shiftRSync q') (MC (shiftAsync n') (shiftAsync m)) Here)
  stepStrA (MC (MC  n m)                  k           ) = Just $ MC n (MC m (shiftAsync k))
  stepStrA (MC (Foc (IR n))               m           ) =
    if not (isCoval m)
      then Just $ HC (IR n) m
      else Nothing
  stepStrA (MC    u           k                 ) = [| MC (stepStrA u) (pure k) |] <|> [| MC (pure u) (stepStrA k) |]

  stepStrA  _                                     = Nothing

  stepStrRS : RSync g a -> Maybe (RSync g a)

  stepStrRS (FHC p (Ax  Here)     ) = Just p
  stepStrRS (FHC p (Ax (There el))) = Just $ Ax el
  stepStrRS (FHC p (IR m)         ) = Just $ IR $ HC (shiftRSync p) (shiftAsync m)
  stepStrRS (FHC p  q             ) = [| FHC (stepStrRS p) (pure q) |] <|> [| FHC (pure p) (stepStrRS q) |]

  stepStrRS  _                      = Nothing

-- STLC conversion

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

encode : Term g a -> Async g a
encode = encodeTm . embedLC

mutual
  forgetAsyncC : Async g a -> Tm g a
  forgetAsyncC (Foc m)     = V $ forgetRSyncC m
  forgetAsyncC (IL p m el) = Let (App (V $ Var el) (V $ forgetRSyncC p)) (forgetAsyncC m)
  forgetAsyncC (HC p m)    = Let (V $ forgetRSyncC p) (forgetAsyncC m)
  forgetAsyncC (MC n m)    = subst1 (forgetAsyncC m) (forgetAsyncC n)

  forgetRSyncC : RSync g a -> Val g a
  forgetRSyncC (Ax el)   = Var el
  forgetRSyncC (IR p)    = Lam $ forgetAsyncC p
  forgetRSyncC (FHC p q) = subst1V (forgetRSyncC q) (forgetRSyncC p)

forget : Async g a -> Term g a
forget = forgetTm . forgetAsyncC

-- reducion + conversion

stepIter : Term [] a -> (Nat, Async [] a)
stepIter = iterCount stepA . encode

stepSIter : Term [] a -> (Nat, Async [] a)
stepSIter = iterCount stepStrA . encode

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

testTm3 : Term [] (A~>A)
testTm3 = (App (App (Lam $ Var Here) (Lam $ Var Here)) (App (Lam $ Var Here) (Lam $ Var Here)))