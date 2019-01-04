module ES.LambdaUpsilon.Umach

import ES.LambdaUpsilon.Untyped

%access public export
%default total

mutual
  Env : Type 
  Env = List (Maybe Clos, Nat)  -- Nothing = Shift

  data Clos = Cl Term Env

Stack : Type
Stack = List Clos

State : Type
State = (Term, Env, Stack)

liftEnv : Env -> Env
liftEnv = map (map S)

step : State -> Maybe State
step (App a b  ,                        e,    p) = Just (a        ,                          e, Cl b e::p) -- AppR
step (Abs a    ,                        e, c::p) = Just (a        , liftEnv e ++ [(Just c, Z)],         p) -- Lambda + Beta 
step (Var  Z   , (Just (Cl a e0), Z  )::e,    p) = Just (a        ,                    e0 ++ e,         p) -- FVar
step (Var (S n), (Just (Cl a e0), Z  )::e,    p) = Just (Var  n   ,                          e,         p) -- RVar  
step (Var  Z   , (c             , S i)::e,    p) = Just (Var  Z   ,                          e,         p) -- FVarLift
step (Var (S n), (c             , S i)::e,    p) = Just (Var  n   ,    (c, i)::(Nothing, Z)::e,         p) -- RVarLift
step (Var  n   , (Nothing       , Z  )::e,    p) = Just (Var (S n),                          e,         p) -- VarShift
step  _                                          = Nothing

{-
mutual
  tau : Env -> List Subs
  tau = map rho

  rho : (Maybe Clos, Nat) -> Subs
  rho (Just (Cl a e), Z  ) = Slash (Clos a (tau e))
  rho (Nothing      , Z  ) = Shift
  rho (c            , S i) = Lift $ rho (c, i)
-}