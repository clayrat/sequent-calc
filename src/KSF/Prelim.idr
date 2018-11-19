module KSF.Prelim

import Data.List
import Data.List.Quantifiers

%access public export
%default total

decNot : DecEq a => {x, y : a} -> Not (x=y) -> (ctra ** decEq x y = No ctra)
decNot {x} {y} nxy with (decEq x y)
  | Yes eq = absurd $ nxy eq
  | No neq = (neq ** Refl)

-- nats

sizeInduction : (f : a -> Nat) -> (p : a -> Type) 
           -> ((x : a) -> ((y : a) -> LT (f y) (f x) -> p y) -> p x) 
           -> (x : a) -> p x
sizeInduction {a} f p step x = step x (g (f x))
  where 
  g : (n : Nat) -> (y : a) -> LT (f y) n -> p y
  g  Z    _ ltfyn = absurd ltfyn
  g (S k) y ltfyn = step y $ \z, ltfzfy => g k z (lteTransitive ltfzfy (fromLteSucc ltfyn))

notLteSucc : Not (LTE (S k) k)
notLteSucc (LTESucc lte) = notLteSucc lte

lteNotEqSucc : LTE k n -> Not (k = S n) 
lteNotEqSucc {k} {n} lte prf = notLteSucc {k=n} $ replace {P=\q=>LTE q n} prf lte

lteNotEqLt : LTE n k -> Not (n=k) -> LT n k
lteNotEqLt         {k=Z}    LTEZero      ctra = absurd $ ctra Refl
lteNotEqLt         {k=S k}  LTEZero      ctra = LTESucc LTEZero
lteNotEqLt {n=S n} {k=S k} (LTESucc lte) ctra = LTESucc $ lteNotEqLt lte (ctra . cong)

islteRefl : (ltk ** isLTE k k = Yes ltk)
islteRefl {k=Z}   = (LTEZero ** Refl)
islteRefl {k=S k} = let (ltk**prf) = islteRefl {k} in (LTESucc ltk ** rewrite prf in Refl)

minusSucc : LTE k n -> minus (S n) k = S (minus n k)
minusSucc _             {n}     {k=Z}   = cong $ sym $ minusZeroRight n
minusSucc (LTESucc lte) {n=S n} {k=S k} = minusSucc lte

islteRight : LTE k n -> (ltk ** isLTE k (S n) = Yes ltk)
islteRight {k} {n} lte with (isLTE k (S n))
  | Yes lt = (lt ** Refl)
  | No ctr = absurd $ ctr $ lteSuccRight lte

islteLT : LT n k -> (ctra ** isLTE k n = No ctra)  
islteLT {k} {n} lt with (isLTE k n)
  | Yes lek = absurd $ notLteSucc $ lteTransitive lt lek
  | No  gtk = (gtk ** Refl)

-- lists  

indexNone : {l : List a} -> LTE (length l) n -> index' n l = Nothing
indexNone {l=[]}    {n=Z}   _   = Refl
indexNone {l=[]}    {n=S _} _   = Refl
indexNone {l=l::ls} {n=Z}   lte = absurd lte
indexNone {l=l::ls} {n=S n} lte = indexNone $ fromLteSucc lte

indexAll : All p xs -> index' k xs = Just y -> p y
indexAll {k=Z}   []        prf = absurd prf
indexAll {k=S k} []        prf = absurd prf
indexAll {k=Z}   (x :: xs) prf = rewrite sym $ justInjective prf in x
indexAll {k=S k} (x :: xs) prf = indexAll xs prf

indexLtJust : (h : List a) -> (n : Nat) -> LT n (length h) -> (x : a ** index' n h = Just x)
indexLtJust []         _    lt = absurd lt
indexLtJust (x :: _)   Z    _  = (x ** Refl)
indexLtJust (_ :: xs) (S k) lt = indexLtJust xs k (fromLteSucc lt)

indexJustLt : (h : List a) -> (n : Nat) -> index' n h = Just x -> LT n (length h)
indexJustLt []         Z    prf = absurd prf
indexJustLt []        (S _) prf = absurd prf
indexJustLt (_ :: _)   Z    _   = LTESucc LTEZero
indexJustLt (_ :: xs) (S k) prf = LTESucc (indexJustLt xs k prf)

indexMapOf : (l : List a) -> (f : a -> b) -> (n : Nat) -> index' n l = Just x -> index' n (map f l) = Just (f x)
indexMapOf []      _ Z     prf = absurd prf
indexMapOf []      _ (S n) prf = absurd prf
indexMapOf (l::ls) f Z     prf = cong {f=Just . f} $ justInjective prf
indexMapOf (l::ls) f (S n) prf = indexMapOf ls f n prf

indexMap : (h : List a) -> (f : a -> b) -> (n : Nat) -> index' n (map f h) = Just x -> (y ** (index' n h = Just y, x = f y))
indexMap []        _  Z    prf = absurd prf
indexMap []        _ (S _) prf = absurd prf
indexMap (y :: _)  _  Z    prf = (y ** (Refl, sym $ justInjective prf))
indexMap (_ :: xs) f (S k) prf = indexMap xs f k prf

indexElem : index' n l = Just x -> Elem x l
indexElem {l=[]}    {n=Z}   prf = absurd prf
indexElem {l=[]}    {n=S n} prf = absurd prf
indexElem {l=l::ls} {n=Z}   prf = rewrite justInjective prf in Here
indexElem {l=l::ls} {n=S n} prf = There $ indexElem prf 

allMap : (a : List x) -> (p : y -> Type) -> (f : x -> y) -> All (\x => p (f x)) a -> All p (map f a)
allMap []        _ _  _        = []
allMap (_ :: xs) p f (a :: as) = a :: allMap xs p f as

elemAll : {p : a -> Type} -> (xs : List a) -> ({x : a} -> Elem x xs -> p x) -> All p xs
elemAll []      f = []
elemAll (x::xs) f = f Here :: elemAll xs (f . There)

indexMid : index' (length as) (as ++ b :: cs) = Just b
indexMid {as=[]}    = Refl
indexMid {as=_::as} = indexMid {as}

consMid : as ++ b :: bs ++ cs = (as ++ [b]) ++ bs ++ cs
consMid {as=[]}    = Refl
consMid {as=a::as} = cong consMid

lenPost : length (as ++ [b]) = S (length as)
lenPost {as} {b} = 
  rewrite lengthAppend as [b] in 
  plusCommutative (length as) 1

-- relations

rcomp : (r : a -> b -> Type) -> (s : b -> c -> Type) -> a -> c -> Type
rcomp r s x z = (y ** (r x y, s y z))

reducible : (r : a -> a -> Type) -> (x : a) -> Type
reducible r x = (x' ** r x x')

functional : (r : a -> b -> Type) -> Type
functional {a} {b} r = (x : a) -> (y, y' : b) -> r x y -> r x y' -> y = y'

stepFunctionAux : (r : a -> b -> Type) -> a -> Maybe b -> Type
stepFunctionAux r x (Just y) = r x y
stepFunctionAux r x Nothing  = (y : b) -> Not (r x y)

stepFunction : (r : a -> b -> Type) -> (f : a -> Maybe b) -> Type
stepFunction {a} {b} r f = (x : a) -> stepFunctionAux r x (f x)

computable : (r : a -> b -> Type) -> Type
computable r = (f ** stepFunction r f)

classical : (r : a -> a -> Type) -> Type
classical {a} r = (s : a) -> Dec (reducible r s)

computableClassical : (r : a -> a -> Type) -> computable r -> classical r
computableClassical r (f ** step) s = aux (step s)
  where 
  aux : stepFunctionAux r s (f s) -> Dec (x' ** r s x')
  aux t with (f s)
    aux t | Just y  = Yes (y ** t)
    aux t | Nothing = No $ \(x ** rsx) => t x rsx

data All2 : (r : a -> b -> Type) -> List a -> List b -> Type where
  Nil2 : All2 r [] []
  Cons2 : (x : a) -> (y : b) -> r x y -> All2 r l1 l2 -> All2 r (x::l1) (y::l2)

all2Impl : (p1, p2 : a -> b -> Type) -> ((x : a) -> (y : b) -> p1 x y -> p2 x y) -> All2 p1 l1 l2 -> All2 p2 l1 l2
all2Impl _  _  _  Nil2            = Nil2
all2Impl p1 p2 f (Cons2 x y a as) = Cons2 x y (f x y a) (all2Impl p1 p2 f as)

data TerminatesOn : (r : a -> a -> Type) -> (x : a) -> Type where
  TerminatesC : ((x' : a) -> r x x' -> TerminatesOn r x') -> TerminatesOn r x

interface ARS t where
  ARS_R : t -> t -> Type

data Evaluates : (r : a -> a -> Type) -> a -> a -> Type where
  EvaluatesB : Not (reducible r x) -> Evaluates r x x
  EvaluatesS : r x y -> Evaluates r y z -> Evaluates r x z  

normalizes : ARS t => (x : t) -> Type
normalizes x = (y ** Evaluates ARS_R x y)

evaluatesFun : ARS t => functional (ARS_R {t}) -> functional (Evaluates (ARS_R {t}))
evaluatesFun _ x x x (EvaluatesB nrx)           (EvaluatesB nry)           = Refl
evaluatesFun _ x x _ (EvaluatesB nrx)           (EvaluatesS {y=b} rxb _)   = absurd $ nrx (b ** rxb)
evaluatesFun _ _ z z (EvaluatesS {y=a} rxa _)   (EvaluatesB nry)           = absurd $ nry (a ** rxa)
evaluatesFun f x y z (EvaluatesS {y=a} rxa eaz) (EvaluatesS {y=b} rxb ebz) = 
  let 
    ab = f x a b rxa rxb 
    eby = replace {P=\q=>Evaluates ARS_R q y} ab eaz 
  in
    evaluatesFun f b y z eby ebz
     
normalizesTerminates : ARS t => functional (ARS_R {t}) -> (x : t) -> normalizes x -> TerminatesOn ARS_R x
normalizesTerminates f x (x**EvaluatesB nrx) = TerminatesC $ \x2, rxx2 => absurd $ nrx (x2**rxx2)
normalizesTerminates f x (y**EvaluatesS {y=a} rxa eay) = TerminatesC $ \x2, rxx2 => 
  rewrite f x x2 a rxx2 rxa in 
  assert_total $ normalizesTerminates f a (y ** eay)  -- smaller arg under sigma strikes again

terminatesNormalizes : ARS t => computable (ARS_R {t}) -> (x : t) -> TerminatesOn ARS_R x -> normalizes x 
terminatesNormalizes comp x (TerminatesC wf) = 
  case computableClassical ARS_R comp x of 
     Yes (y ** axy) => 
       let (z**eyz) = terminatesNormalizes comp y (wf y axy) in 
       (z ** EvaluatesS axy eyz)
     No ct => (x ** EvaluatesB ct)

evaluatesIrred : ARS t => (x, y : t) -> Evaluates ARS_R x y -> Not (reducible ARS_R y)
evaluatesIrred x x (EvaluatesB nrx)         = nrx
evaluatesIrred _ y (EvaluatesS {y=a} _ eaz) = evaluatesIrred a y eaz

-- misc

noneHolds : List Type -> Type
noneHolds []      = ()
noneHolds (p::ps) = (Not p, noneHolds ps)

exactlyOneHolds : List Type -> Type
exactlyOneHolds [] = Void
exactlyOneHolds (p::ps) = Either (p, noneHolds ps) (Not p, exactlyOneHolds ps)

decEqDiffIsNo : DecEq a => {x, y : a} -> Not (x=y) -> (contra ** decEq x y = No contra)
decEqDiffIsNo {x} {y} contra with (decEq x y)
  decEqDiffIsNo {x} {y=x} contra | Yes Refl = absurd $ contra Refl
  decEqDiffIsNo {x} {y} contra   | No c = (c ** Refl)