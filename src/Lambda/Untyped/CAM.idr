module Lambda.Untyped.CAM

%default total
%access public export

data Term = Var Nat
          | Lam Term
          | App Term Term
          | Nil
          | Cons Term Term
          | Car Term
          | Cdr Term

data Val = Null | Pair Val Val | Cl Val Term

data Ctx = C0 
         | C1 Term Ctx
         | C2 Ctx
         | C3 Term Ctx
         | C4 Ctx
         | C5 Ctx
         | C6 Ctx

Stack : Type
Stack = List Val

State : Type
State = Either (Term, Val, Stack, Ctx) (Ctx, Val, Stack)

proj : Nat -> Val -> Val
proj  Z    (Pair a b) = b
proj (S n) (Pair a b) = proj n a
proj  _     _         = Null

step : State -> Maybe State
step (Left (Var n   ,       v ,         s, k)) = Just $ Right (k, proj n v, s)
step (Left (Lam t   ,       v ,         s, k)) = Just $ Right (k, Cl v t, s)
step (Left (Nil     ,       _ ,         s, k)) = Just $ Right (k, Null, s)
step (Left (App t u ,       v ,         s, k)) = Just $ Left (t, v, v::s, C1 u k)
step (Left (Cons t u,       v ,         s, k)) = Just $ Left (t, v, v::s, C3 u k)
step (Left (Car t   ,       v ,         s, k)) = Just $ Left (t, v, s, C5 k)
step (Left (Cdr t   ,       v ,         s, k)) = Just $ Left (t, v, s, C6 k)
step (Right (C1 t k ,       v ,     v1::s)) = Just $ Left (t, v1, v::s, C2 k)
step (Right (C2 k   ,       v1, Cl v t::s)) = Just $ Left (t, Pair v v1, s, k)
step (Right (C3 t1 k,       v ,     v1::s)) = Just $ Left (t1, v1, v::s, C4 k)
step (Right (C4 k   ,       v ,     v1::s)) = Just $ Right (k, Pair v1 v, s)
step (Right (C5 k   , Pair v _,         s)) = Just $ Right (k, v, s)
step (Right (C6 k   , Pair _ v,         s)) = Just $ Right (k, v, s)
step _                                      = Nothing
