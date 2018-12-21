module MuKAM

%access public export
%default total

data Term = Var Nat 
          | Lam Term
          | App Term Term
          | Mu Term
          | Named Nat Term

mutual
  Env : Type
  Env = (List Clos, List Stk)

  data Clos = Cl Term Env

  Stk : Type
  Stk = List Clos

State : Type
State = (Term, Env, Stk)

step : State -> Maybe State
step (Var  Z   , (Cl t e::_, _),    s) =   Just (    t,             e,         s)
step (Var (S n),      (_::e,es),    s) =   Just (Var n,    (e,    es),         s)
step (Lam t    ,         (e,es), c::s) =   Just (    t, (c::e,    es),         s)
step (App t u  ,              e,    s) =   Just (    t,             e, Cl u e::s)
step (Mu c     ,         (e,es),    s) =   Just (    c,     (e,s::es),        [])
step (Named n t,         (e,es),   []) = (\s => (    t,     (e,   es),         s)) <$> index' n es 
step  _                           = Nothing

stepIter : State -> (Nat, Maybe State)
stepIter s = loop Z s
  where
  loop : Nat -> State -> (Nat, Maybe State)
  loop n s1 = case step s1 of
    Nothing => (n, Just s1)
    Just s2 => assert_total $ loop (S n) s2

run : Term -> (Nat, Maybe State)
run t = stepIter (t, ([], []), [])

pierce : Term 
pierce = Lam $ Mu $ Named 0 $ App (Var 0) (Lam $ Mu $ Named 1 (Var 0))

contrapos : Term
contrapos = Lam $ Lam $ Mu $ App (App (Var 1) (Lam $ Named 0 $ Var 0)) (Var 0)