module ES.LambdaUpsilon

%access public export
%default total

-- binary trees
data BTree = Leaf
           | Left BTree
           | Right BTree
           | BNode BTree BTree

btreeSize : BTree -> Nat
btreeSize  Leaf         = 1
btreeSize (Left t)      = S (btreeSize t)
btreeSize (Right t)     = S (btreeSize t)
btreeSize (BNode lt rt) = S (btreeSize lt + btreeSize rt)

mutual 
  data Term : Type where
    Abs   : Term -> Term
    Index : Nat -> Term
    App   : Term -> Term -> Term
    Clos  : Term -> Subs -> Term

  -- explicit substitutions 
  data Subs : Type where
    Lift  : Subs -> Subs
    Slash : Term -> Subs
    Shift : Subs

Uninhabited (Lift _ = Slash _) where
  uninhabited Refl impossible

liftInj : Lift x = Lift y -> x = y  
liftInj Refl = Refl

mutual 
  termSize : Term -> Nat
  termSize (Index ix)  = S ix
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
liftsDiff  Z    s t prf = uninhabited prf
liftsDiff (S k) s t prf = liftsDiff k s t $ liftInj prf

-- lifts is injective
liftsInj : (n : Nat) -> (s, t : Subs) -> lifts n s = lifts n t -> s = t
liftsInj  Z    s t prf = prf
liftsInj (S k) s t prf = liftsInj k s t $ liftInj prf

-- translation from btrees to terms
mutual
  btree2Term : BTree -> Term
  btree2Term  Leaf         = Index Z
  btree2Term (Left t)      = btree2Term' 1 t
  btree2Term (Right t)     = Abs $ btree2Term t
  btree2Term (BNode lt rt) = App (btree2Term lt) (btree2Term rt)

  btree2Term' : Nat -> BTree -> Term
  btree2Term' n  Leaf         = Index n
  btree2Term' n (Left t)      = btree2Term' (S n) t
  btree2Term' n (Right t)     = Clos (btree2Term t) (lifts (n `minus` 1) Shift)
  btree2Term' n (BNode lt rt) = Clos (btree2Term rt) (lifts (n `minus` 1) (Slash $ btree2Term lt))

-- translation preserves the structure size
sizeProp : (bt : BTree) -> (n : Nat) -> (termSize (btree2Term bt) = btreeSize bt, termSize (btree2Term' (S n) bt) = (S n) + btreeSize bt)
sizeProp  Leaf          n    = (Refl, rewrite plusCommutative n 1 in Refl)
sizeProp (Left t)       Z    = (snd $ sizeProp t Z, snd $ sizeProp t (S Z))
sizeProp (Left t)      (S k) = (snd $ sizeProp t Z, rewrite plusAssociative k 1 (btreeSize t) in 
                                                    rewrite plusCommutative k 1 in 
                                                    snd $ sizeProp t (S (S k)))
sizeProp (Right t)      Z    = rewrite fst $ sizeProp t Z in 
                               (Refl, rewrite plusCommutative (btreeSize t) 1 in Refl)
sizeProp (Right t)     (S k) = rewrite fst $ sizeProp t Z in 
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