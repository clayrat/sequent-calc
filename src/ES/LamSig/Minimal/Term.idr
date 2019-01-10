module ES.LamSig.Minimal.Term

import Lambda.Untyped.Term

%access public export
%default total

mutual 
  data Tm : Type where 
    Var  : Tm                    -- Var i ~ i[^ * ... * ^]
    Lam  : Tm -> Tm 
    App  : Tm -> Tm -> Tm
    Clos : Tm -> Subs -> Tm 

  data Subs : Type where
    Id    : Subs 
    Shift : Subs 
    Cons  : Tm -> Subs -> Subs
    Comp  : Subs -> Subs -> Subs

termLS : Term -> Tm    
termLS (Var  Z)    = Var
termLS (Var (S n)) = Clos (assert_total $ termLS $ Var n) Shift
termLS (Lam t)     = Lam $ termLS t
termLS (App t1 t2) = App (termLS t1) (termLS t2)

{-
-- TODO scoped

mutual 
  data Term : Nat -> Type where
    Var  : Term n                        
    Lam  : Term (S n) -> Term n
    App  : Term n -> Term n -> Term n
    Clos : Term n -> Subs k n -> Term k

  data Subs : Nat -> Nat -> Type where
    Id    : Subs n n
    Shift : Subs (S n) n
    Cons  : Term n -> Subs n k -> Subs n (S k)
    Comp  : Subs n m -> Subs m k -> Subs n k

data RedexT : Term n -> Term n -> Type where
  R1  : RedexT (App (Lam a) b)       (Clos a (Cons b Id))  
  R2  : RedexT (Clos (App a b) s)    (App (Clos a s) (Clos b s))  
  R3  : RedexT (Clos Var (Cons a s))  a
  R4  : RedexT (Clos (Clos a s) t)   (Clos a (Comp s t))
  R5  : RedexT (Clos (Lam a) s)      (Lam (Clos a (Cons Var (Comp s Shift))))
  R10 : RedexT (Clos a Id)            a

data RedexS : Subs n m -> Subs n m -> Type where  
  R6  : RedexS (Comp Id s)                         s
  R7  : RedexS (Comp Shift (Cons a s))             s
  R8  : RedexS (Comp (Comp s1 s2) s3)             (Comp s1 (Comp s2 s3))
  R9  : RedexS (Comp (Cons a s) t)                (Cons (Clos a t) (Comp s t))
  R11 : RedexS (Comp s Id)                         s
  R12 : RedexS (Cons Var Shift)                    Id
  R13 : RedexS (Cons (Clos Var s) (Comp Shift s))  s
-}

