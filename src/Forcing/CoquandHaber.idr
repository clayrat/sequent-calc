module Forcing.CoquandHaber

-- quite close to an ordinary evaluation program for Godel system T by head reduction.
-- The monad we use is a composition of the list monad (for nondeterminism) and of the state monad

%access public export
%default total

Name : Type
Name = String

data Exp = Zero
         | One
         | Succ Exp
         | App Exp Exp
         | Natrec Exp Exp
         | Boolrec Exp Exp
         | Lam Name Exp
         | Var Name
         | Gen

Show Exp where
  show  Zero         = "0"
  show  One          = "1"
  show (Succ e)      = "S" ++ show e
  show (App t u)     = "(" ++ show t ++ ")@(" ++ show u ++ ")"
  show (Natrec t u)  = "NR(" ++ show t ++ ", " ++ show u ++ ")"
  show (Boolrec t u) = "BR(" ++ show t ++ ", " ++ show u ++ ")"
  show (Lam n t)     = "\\" ++ n ++ "." ++ show t
  show (Var n)       = n
  show  Gen          = "?"

-- closed substitution

subst : Exp -> Name -> Exp -> Exp
subst t@(Var y)         x e = if x == y then e else t
subst t@(Lam y t1)      x e = if x == y then t else Lam y (subst t1 x e)
subst   (App t1 t2)     x e = App (subst t1 x e) (subst t2 x e)
subst   (Natrec t1 t2)  x e = Natrec (subst t1 x e) (subst t2 x e)
subst   (Boolrec t1 t2) x e = Boolrec (subst t1 x e) (subst t2 x e)
subst   (Succ t1)       x e = Succ (subst t1 x e)
subst t                 _ _ = t

Cond : Type
Cond = List (Int,Exp)   -- uses only Zero or One

data M a = MM (Cond -> List (Cond, a))

app : M a -> Cond -> List (Cond, a)
app (MM f) p = f p

Functor M where
  map f (MM t) = MM $ (map (map f)) . t

Applicative M where
  pure x = MM $ \p => [(p,x)]
  f <*> t = MM $ \p => concatMap (\(q,a) => map (\(r,g) => (r, g a)) (app f q))
                                 (app t p)

Monad M where
  l >>= k = MM $ \p => concatMap (\(q,a) => app (k a) q)
                                 (app l p)

-- split determines if the condition p contains the value in k,
-- and otherwise forks between the two possibilities

split : Int -> M Exp
split k = MM $ \p => case lookup k p of
                       Just b => [(p,b)]
                       Nothing => [ ((k,Zero)::p,Zero)
                                  , ((k,One)::p,One)
                                  ]

mutual
  partial
  -- gen k e computes e before applying it to split
  gen : Int -> Exp -> M Exp
  gen k  Zero    = split k
  gen k (Succ e) = gen (k+1) e
  gen k  e       = do e' <- step e
                      gen k e'

  partial
  -- step implements the reduction
  step : Exp -> M Exp
  step (App (Lam x t)        u      ) = pure (subst t x u)
  step (App (Natrec t0 t1)   Zero   ) = pure t0
  step (App (Natrec t0 t1)  (Succ t)) = pure (App (App t1 t) (App (Natrec t0 t1) t))
  step (App (Boolrec t0 t1)  Zero   ) = pure t0
  step (App (Boolrec t0 t1)  One    ) = pure t1
  step (App (Natrec t0 t1)   t      ) = App (Natrec t0 t1) <$> step t
  step (App (Boolrec t0 t1)  t      ) = App (Boolrec t0 t1) <$> step t
  step (App  Gen             u      ) = gen 0 u
  step (App  t               u      ) = (\t' => App t' u) <$> step t

-- app (eval t) [] outputs a covering of
-- Cantor space if t is of type N2

partial
eval : Exp -> M Exp
eval Zero = pure Zero
eval One  = pure One
eval t    = do t' <- step t
               eval t'