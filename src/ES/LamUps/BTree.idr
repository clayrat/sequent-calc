module ES.LamUps.BTree

import ES.LamUps.Untyped

%access public export
%default total

Uninhabited (Var _ = Abs _) where
  uninhabited Refl impossible

Uninhabited (Abs _ = Var _) where
  uninhabited Refl impossible

Uninhabited (Abs _ = App _ _) where
  uninhabited Refl impossible

Uninhabited (App _ _ = Abs _) where
  uninhabited Refl impossible

Uninhabited (Clos _ _ = Abs _) where
  uninhabited Refl impossible

Uninhabited (Var _ = App _ _) where
  uninhabited Refl impossible

Uninhabited (App _ _ = Var _) where
  uninhabited Refl impossible

Uninhabited (Clos _ _ = Var _) where
  uninhabited Refl impossible

Uninhabited (Var _ = Clos _ _) where
  uninhabited Refl impossible

Uninhabited (Clos _ _ = App _ _) where
  uninhabited Refl impossible

absInj : Abs x = Abs y -> x = y
absInj Refl = Refl

appInj : App a b = App c d -> (a = c, b = d)
appInj Refl = (Refl, Refl)

closInj : Clos a b = Clos c d -> (a = c, b = d)
closInj Refl = (Refl, Refl)

Uninhabited (Lift _ = Slash _) where
  uninhabited Refl impossible

Uninhabited (Lift _ = Shift) where
  uninhabited Refl impossible

liftInj : Lift x = Lift y -> x = y  
liftInj Refl = Refl

slashInj : Slash x = Slash y -> x = y  
slashInj Refl = Refl

mutual 
  termSize : Term -> Nat
  termSize (Var ix)    = S ix
  termSize (Abs t)     = S (termSize t)
  termSize (App lt rt) = S (termSize lt + termSize rt)
  termSize (Clos t s)  = S (termSize t + subsSize s)    
 
  subsSize : Subs -> Nat
  subsSize (Lift s)  = S (subsSize s)
  subsSize (Slash t) = S (termSize t)
  subsSize  Shift    = 1

-- auxiliary lifts helper
lifts : Nat -> Subs -> Subs
lifts  Z    s = s
lifts (S n) s = Lift (lifts n s)

-- auxiliary lifts lemmas 
liftsSize : (n : Nat) -> (s : Subs) -> subsSize (lifts n s) = n + subsSize s
liftsSize  Z    s = Refl
liftsSize (S k) s = cong $ liftsSize k s

liftsInd : (n : Nat) -> (s : Subs) -> lifts (S n) s = lifts n (Lift s)
liftsInd  Z    s = Refl
liftsInd (S k) s = cong $ liftsInd k s

liftsDiff : (n : Nat) -> (s : Subs) -> (t : Term) -> Not (Lift (lifts n s) = lifts n (Slash t))
liftsDiff  Z    s t = uninhabited
liftsDiff (S k) s t = liftsDiff k s t . liftInj

liftsDiffS : (n : Nat) -> (s : Subs) -> Not (Lift (lifts n s) = lifts n Shift)
liftsDiffS  Z    s = uninhabited
liftsDiffS (S n) s = liftsDiffS n s . liftInj

-- lifts is injective
liftsInj : (n : Nat) -> (s, t : Subs) -> lifts n s = lifts n t -> s = t
liftsInj  Z    s t prf = prf
liftsInj (S k) s t prf = liftsInj k s t $ liftInj prf    

-- binary trees
data BTree = Leaf
           | LTree BTree
           | RTree BTree
           | BNode BTree BTree

btreeSize : BTree -> Nat
btreeSize  Leaf         = 1
btreeSize (LTree t)     = S (btreeSize t)
btreeSize (RTree t)     = S (btreeSize t)
btreeSize (BNode lt rt) = S (btreeSize lt + btreeSize rt)

-- translation from btrees to terms
mutual
  btree2Term : BTree -> Term
  btree2Term  Leaf         = Var Z
  btree2Term (LTree t)     = btree2TermN 1 t
  btree2Term (RTree t)     = Abs $ btree2Term t
  btree2Term (BNode lt rt) = App (btree2Term lt) (btree2Term rt)

  btree2TermN : Nat -> BTree -> Term
  btree2TermN n  Leaf         = Var n
  btree2TermN n (LTree t)     = btree2TermN (S n) t
  btree2TermN n (RTree t)     = Clos (btree2Term t) (lifts (n `minus` 1) Shift)
  btree2TermN n (BNode lt rt) = Clos (btree2Term rt) (lifts (n `minus` 1) (Slash $ btree2Term lt))

-- translation preserves the structure size
sizeProp : (bt : BTree) -> (n : Nat) -> (termSize (btree2Term bt) = btreeSize bt, termSize (btree2TermN (S n) bt) = (S n) + btreeSize bt)
sizeProp  Leaf          n    = (Refl, rewrite plusCommutative n 1 in Refl)
sizeProp (LTree t)      Z    = (snd $ sizeProp t Z, snd $ sizeProp t (S Z))
sizeProp (LTree t)     (S k) = (snd $ sizeProp t Z, rewrite plusAssociative k 1 (btreeSize t) in 
                                                   rewrite plusCommutative k 1 in 
                                                   snd $ sizeProp t (S (S k)))
sizeProp (RTree t)      Z    = rewrite fst $ sizeProp t Z in 
                               (Refl, rewrite plusCommutative (btreeSize t) 1 in Refl)
sizeProp (RTree t)     (S k) = rewrite fst $ sizeProp t Z in 
                               (Refl, rewrite liftsSize k Shift in  
                                      rewrite plusCommutative (btreeSize t) (S (plus k 1)) in
                                      rewrite plusAssociative k 1 (btreeSize t) in 
                                      Refl)
sizeProp (BNode lt rt)  Z    = rewrite fst $ sizeProp lt Z in 
                               rewrite fst $ sizeProp rt Z in
                               (Refl, rewrite plusCommutative (btreeSize rt) (S (btreeSize lt)) in 
                                      Refl)
sizeProp (BNode lt rt) (S k) = rewrite fst $ sizeProp lt Z in 
                               rewrite fst $ sizeProp rt Z in 
                               (Refl, rewrite liftsSize k (Slash (btree2Term lt)) in  
                                      rewrite fst $ sizeProp lt Z in  
                                      rewrite plusCommutative (btreeSize rt) (S (plus k (S (btreeSize lt)))) in
                                      cong {f=S . S} $ sym $ plusAssociative k (S (btreeSize lt)) (btreeSize rt))

-- structural invariant of btree_to_term'
btree2TermNInv : (bt : BTree) -> (n : Nat) -> Either (btree2TermN (S n) bt = Var (n + btreeSize bt))
                                                     (t ** s ** btree2TermN (S n) bt = Clos t (lifts n s))
btree2TermNInv  Leaf       n = Left $ cong $ plusCommutative 1 n
btree2TermNInv (LTree x)   n = case btree2TermNInv x (S n) of 
  Left prf             => Left $ rewrite plusAssociative n 1 (btreeSize x) in 
                                 rewrite plusCommutative n 1 in
                                 prf
  Right (t ** s ** prf) => Right (t ** Lift s ** rewrite sym $ liftsInd n s in prf)
btree2TermNInv (RTree x)   n = Right (btree2Term x ** Shift ** rewrite minusZeroRight n in Refl)
btree2TermNInv (BNode x y) n = Right (btree2Term y ** Slash (btree2Term x) ** rewrite minusZeroRight n in Refl)

-- auxiliary size lemmas
contrapositive : (p -> q) -> (Not q -> Not p)
contrapositive pq nq = nq . pq

-- auxiliary proof arguments
diffTermSize : Not (termSize t = termSize t1) -> Not (t = t1)
diffTermSize = contrapositive cong

diffSubsSize : Not (subsSize s = subsSize s1) -> Not (s = s1)
diffSubsSize = contrapositive cong

-- positive size lemmas
positiveBtreeSize : (bt : BTree) -> Not (btreeSize bt = 0)
positiveBtreeSize  Leaf       = uninhabited
positiveBtreeSize (LTree x)   = uninhabited
positiveBtreeSize (RTree x)   = uninhabited
positiveBtreeSize (BNode x y) = uninhabited

positiveTermSize : (t : Term) -> Not (termSize t = 0)
positiveTermSize (Abs x)    = uninhabited
positiveTermSize (Var k)    = uninhabited
positiveTermSize (App x y)  = uninhabited
positiveTermSize (Clos x y) = uninhabited

-- additional structural invariants of btree_to_term'
btree2TermNAbs : (bt, bt1 : BTree) -> (n : Nat) -> Not (btree2TermN (S n) bt = Abs (btree2Term bt1))
btree2TermNAbs  Leaf       bt1 n = uninhabited
btree2TermNAbs (LTree x)   bt1 n = btree2TermNAbs x bt1 (S n)
btree2TermNAbs (RTree x)   bt1 n = uninhabited
btree2TermNAbs (BNode x y) bt1 n = uninhabited

btree2TermNApp : (bt, bt1, bt2 : BTree) -> (n : Nat) -> Not (btree2TermN (S n) bt = App (btree2Term bt1) (btree2Term bt2))
btree2TermNApp  Leaf       bt1 bt2 n = uninhabited
btree2TermNApp (LTree x)   bt1 bt2 n = btree2TermNApp x bt1 bt2 (S n)
btree2TermNApp (RTree x)   bt1 bt2 n = uninhabited
btree2TermNApp (BNode x y) bt1 bt2 n = uninhabited

btree2TermNLTreeRTree : (n : Nat) -> (bt, bt1 : BTree) -> Not (btree2TermN (S n) (LTree bt) = btree2TermN (S n) (RTree bt1))
btree2TermNLTreeRTree n bt bt1 prf with (btree2TermNInv bt (S n))
  | Left lprf              = uninhabited $ trans (sym lprf) prf
  | Right (t ** s ** rprf) = 
    let prf2 = snd $ closInj $ trans (sym rprf) prf in 
    liftsDiffS n s $ replace {P=\q=>Lift (lifts n s) = lifts q Shift} (minusZeroRight n) prf2

btree2TermNLTreeBNode : (n : Nat) -> (bt, bt1, bt2 : BTree) -> Not (btree2TermN (S n) (LTree bt) = btree2TermN (S n) (BNode bt1 bt2))
btree2TermNLTreeBNode n bt bt1 bt2 prf with (btree2TermNInv bt (S n))
  | Left lprf              = uninhabited $ trans (sym lprf) prf
  | Right (t ** s ** rprf) = 
    let prf2 = snd $ closInj $ trans (sym rprf) prf in 
    liftsDiff n s (btree2Term bt1) $ replace {P=\q=>Lift (lifts n s) = lifts q (Slash (btree2Term bt1))} (minusZeroRight n) prf2

btree2TermNRTreeBNode : (n : Nat) -> (bt, bt1, bt2 : BTree) -> Not (btree2TermN (S n) (RTree bt) = btree2TermN (S n) (BNode bt1 bt2))
btree2TermNRTreeBNode n bt bt1 bt2 = 
  rewrite minusZeroRight n in 
  diffSubsSize {s=lifts n Shift} {s1=lifts n (Slash (btree2Term bt1))}
    (rewrite liftsSize n Shift in 
     rewrite liftsSize n (Slash (btree2Term bt1)) in
     rewrite sym $ plusZeroRightNeutral (n+1) in
     rewrite plusAssociative n 1 (termSize (btree2Term bt1)) in
     positiveTermSize (btree2Term bt1) . sym . plusLeftCancel (n+1) Z (termSize (btree2Term bt1))
    ) . snd . closInj
    
-- main proof: translation is injective
injectionProp : (bt, bt1 : BTree) -> ( btree2Term bt = btree2Term bt1 -> bt = bt1
                                     , (n : Nat) -> btree2TermN (S n) bt = btree2TermN (S n) bt1 -> bt = bt1
                                     )
injectionProp  Leaf        Leaf         = (\_ => Refl, \_, _ => Refl)
injectionProp  Leaf       (LTree l1)    = (absurd . diffTermSize {t=Var 0} {t1=btree2TermN 1 l1} 
                                                     (rewrite fst $ sizeProp (LTree l1) 0 in 
                                                      positiveBtreeSize l1 . sym . succInjective Z (btreeSize l1))
                                         ,\n => absurd . diffTermSize {t=Var (S n)} {t1=btree2TermN (S (S n)) l1} 
                                                           (rewrite snd $ sizeProp (LTree l1) n in 
                                                            rewrite plusAssociative n 1 (btreeSize l1) in
                                                            rewrite plusCommutative n 1 in
                                                            rewrite sym $ plusZeroRightNeutral (S (S n)) in
                                                            positiveBtreeSize l1 . sym . plusLeftCancel (2+n) Z (btreeSize l1)))
injectionProp  Leaf       (RTree r1)    = (absurd, \_ => absurd)
injectionProp  Leaf       (BNode l1 r1) = (absurd, \_ => absurd)
injectionProp (LTree l)    Leaf         = (absurd . diffTermSize {t=btree2TermN 1 l} {t1=Var 0} 
                                                     (rewrite fst $ sizeProp (LTree l) 0 in 
                                                      positiveBtreeSize l . succInjective (btreeSize l) Z) 
                                         ,\n => absurd . diffTermSize {t=btree2TermN (S (S n)) l} {t1=Var (S n)} 
                                                           (rewrite snd $ sizeProp (LTree l) n in 
                                                            rewrite plusAssociative n 1 (btreeSize l) in
                                                            rewrite plusCommutative n 1 in
                                                            rewrite sym $ plusZeroRightNeutral (S (S n)) in
                                                            positiveBtreeSize l . plusLeftCancel (2+n) (btreeSize l) Z))
injectionProp (LTree l)   (LTree l1)     = let ih = snd $ injectionProp l l1 in 
                                         (cong . ih 0, \n => cong . ih (S n))
injectionProp (LTree l)   (RTree r1)    = (absurd . btree2TermNAbs l r1 Z, \n => absurd . btree2TermNLTreeRTree n l r1)
injectionProp (LTree l)   (BNode l1 r1) = (absurd . btree2TermNApp l l1 r1 Z, \n => absurd . btree2TermNLTreeBNode n l l1 r1)
injectionProp (RTree r)    Leaf         = (absurd, \_ => absurd)
injectionProp (RTree r)   (LTree l1)    = (absurd . btree2TermNAbs l1 r Z . sym, \n => absurd . btree2TermNLTreeRTree n l1 r . sym)
injectionProp (RTree r)   (RTree r1)    = let ih = fst $ injectionProp r r1 in 
                                          (cong . ih . absInj, \_ => cong . ih . fst . closInj)
injectionProp (RTree r)   (BNode l1 r1) = (absurd, \n => absurd . btree2TermNRTreeBNode n r l1 r1)
injectionProp (BNode l r)  Leaf         = (absurd, \_ => absurd)
injectionProp (BNode l r) (LTree l1)    = (absurd . btree2TermNApp l1 l r Z . sym, \n => absurd . btree2TermNLTreeBNode n l1 l r . sym)
injectionProp (BNode l r) (RTree r1)    = (absurd, \n => absurd . btree2TermNRTreeBNode n r1 l r . sym)
injectionProp (BNode l r) (BNode l1 r1) = let 
                                            ihl = fst $ injectionProp l l1
                                            ihr = fst $ injectionProp r r1
                                           in
                                          ( \prf => let (lprf, rprf) = appInj prf in 
                                            rewrite ihl lprf in 
                                            rewrite ihr rprf in 
                                            Refl
                                          , \n => rewrite minusZeroRight n in
                                            \prf => let (rprf, lprf) = closInj prf in 
                                            rewrite ihl $ slashInj $ liftsInj n (Slash (btree2Term l)) (Slash (btree2Term l1)) lprf in 
                                            rewrite ihr rprf in
                                            Refl)
