module Lambda.STLC.Term

import Data.List.Elem
import Elem

import Lambda.STLC.Ty
import Lambda.Untyped.Term

%default total

public export
data Term : List Ty -> Ty -> Type where
  Var : Elem a g -> Term g a
  Lam : Term (a::g) b -> Term g (a~>b)
  App : Term g (a~>b) -> Term g a -> Term g b

isVal : Term g a -> Bool
isVal (Lam _) = True
isVal (Var _) = True
isVal  _      = False

forget : Term g a -> Term
forget (Var el)    = Var $ elem2Nat el
forget (Lam t)     = Lam $ forget t
forget (App t1 t2) = App (forget t1) (forget t2)

-- examples

export
TestTy : Ty
TestTy = A~>A

export
TestTm0 : Term [] TestTy
TestTm0 = App (Lam $ Var Here) (Lam $ Var Here)

export
TestTm1 : Term [] TestTy
TestTm1 = App (App (Lam $ Var Here) (Lam $ Var Here)) (Lam $ Var Here)

test1 : forget TestTm1 = Term1
test1 = Refl

-- (λx.x) ((λx.x) (λx.x))
TestTm2 : Term [] TestTy
TestTm2 = App (Lam $ Var Here) (App (Lam $ Var Here) (Lam $ Var Here))

test2 : forget TestTm2 = Term2
test2 = Refl

ResultTm : Term [] TestTy
ResultTm = Lam $ Var Here

-- scott

export
NumTy : Ty
NumTy = A~>(A~>A)~>A

zero : Term [] NumTy
zero = Lam $ Lam $ Var $ There Here

export
succ : Term [] (NumTy~>A~>(NumTy~>NumTy)~>NumTy)
succ = Lam $ Lam $ Lam $ App (Var Here) (Var $ There $ There Here)

succzero : Term [] (A~>(NumTy~>NumTy)~>NumTy)
succzero = App succ zero

-- church

NumTy' : Ty
NumTy' = (A~>A)~>(A~>A)

zero' : Term [] NumTy'
zero' = Lam $ Lam $ Var Here

one' : Term [] NumTy'
one' = Lam $ Lam $ App (Var $ There Here) (Var Here)

two' : Term [] NumTy'
two' = Lam $ Lam $ App (Var $ There Here) (App (Var $ There Here) (Var Here))

succ' : Term [] (NumTy' ~> NumTy')
succ' = Lam $ Lam $ Lam $ App (Var $ There Here) (App (App (Var $ There $ There Here) (Var $ There Here)) (Var Here))

Sc : Term [] ((A~>(A~>A)~>A) ~> (A~>A~>A) ~> (A~>A))
Sc = Lam $ Lam $ Lam $ App (App (Var $ There $ There Here) (Var Here)) (App (Var $ There Here) (Var Here))

-- λx.λy.x, constant function, aka K combinator
Kc1 : Term [] (A~>(A~>A)~>A)
Kc1 = Lam $ Lam $ Var $ There Here

Kc2 : Term [] (A~>A~>A)
Kc2 = Lam $ Lam $ Var $ There Here
