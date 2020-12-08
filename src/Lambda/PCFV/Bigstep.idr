module Lambda.PCFV.Bigstep

import Data.List.Quantifiers
import Lambda.PCFV.Term

%default total

mutual
  Env : List Ty -> Type
  Env = All Res

  data Res : Ty -> Type where
    RZ  : Res A
    RS  : Res A -> Res A
    RC  : Res a -> Res (C a)
    RF  : Env g -> Comp (C a::g) a -> Res (C a)
    RCl : Env g -> Comp (a::g) b -> Res (a~>b)

mutual
  evalV : Val g a -> Env g -> Res a
  evalV (Var el) env = indexAll el env
  evalV  Zero    _   = RZ
  evalV (Succ v) env = RS $ evalV v env
  evalV (Lam t)  env = RCl env t
  evalV (Fix t)  env = RF env t
  evalV (Wrap t) env = RC $ evalC t env

  evalC : Comp g a -> Env g -> Res a
  evalC (V v)       env = evalV v env
  evalC (App t u)   env = case evalV t env of
    RCl env' c => assert_total $
                  evalC c (evalV u env :: env')
  evalC (If0 t u v) env = case evalV t env of
    RZ   => evalC u env
    RS r => evalC v (r :: env)
  evalC (Bnd v c)   env = case evalV v env of
                            RC r => evalC c (r :: env)
                            RF env' t => assert_total $
                                         evalC c (evalC t (RF env' t :: env') :: env)
