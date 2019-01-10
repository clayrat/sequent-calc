module ES.LamSig.Minimal.KAM

import Lambda.Untyped.Term
import Lambda.Untyped.Strong.KN
import ES.LamSig.Minimal.Term

%default total
%access public export

-- KN embedding

termLSi : TermN -> Nat -> Tm    
termLSi (T (App t1 t2)) m = App (assert_total $ termLSi (T t1) m) (assert_total $ termLSi (T t2) m)
termLSi (T (Lam t))     m = Lam $ assert_total $ termLSi (T t) (S m)
termLSi (T (Var  Z))    m = Var
termLSi (T (Var (S n))) m = Clos (assert_total $ termLSi (T $ Var n) m) Shift
termLSi (V n)           m = assert_total $ termLSi (T $ Var (minus m n)) m
termLSi (M t)           m = Var -- what to put here?

mutual 
  closLS : Clos -> Nat -> Tm
  closLS (Cl t e) m = Clos (termLSi t m) (envLS e m)

  envLS : Env -> Nat -> Subs
  envLS []     _ = Id
  envLS (c::e) m = Cons (closLS c m) (envLS e m)

stkRec : Tm -> Stack -> Nat -> Tm  
stkRec t               []  _ = t
stkRec t          (C c::s) m = stkRec (App t (closLS c m)) s m
stkRec t            (L::s) m = stkRec (Lam t) s m
stkRec t (MM (Mk t1 j)::s) _ = stkRec (App (termLSi (T t1) j) t) s j  -- is this correct?

stateLS : State -> Tm
stateLS (More t e s i) = stkRec (Clos (termLSi t i) (envLS e i)) s i
stateLS (Done t)       = termLSi (T t) Z  -- is this correct?
