module LambdaMu.SmallstepNam

import Control.Monad.Syntax
import Control.Monad.Identity
import Control.Monad.Writer

%access public export
%default total

data Any = GetAny Bool

Semigroup Any where
  (GetAny a) <+> (GetAny b) = GetAny (a || b)

Monoid Any where
  neutral = GetAny False

runWriter : Writer w a -> (a, w)
runWriter = runIdentity . runWriterT  

data TermType = Named | Unnamed

TVar : Type
TVar = String

MuVar : Type
MuVar = String

data Expr : TermType -> Type where
  Var : TVar -> Expr Unnamed
  Lam : TVar -> Expr Unnamed -> Expr Unnamed
  App : Expr Unnamed -> Expr Unnamed -> Expr Unnamed
  Freeze : MuVar -> Expr Unnamed -> Expr Named
  Mu : MuVar -> Expr Named -> Expr Unnamed

substU : TVar -> Expr Unnamed -> Expr n -> Expr n
substU x e = go
  where
    go : Expr n -> Expr n
    go (Var y) = if y == x then e else Var y
    go (Lam y e) = Lam y $ if y == x then e else go e
    go (App f e) = App (go f) (go e)
    go (Freeze alpha e) = Freeze alpha (go e)
    go (Mu alpha u) = Mu alpha (go u)

renameN : MuVar -> MuVar -> Expr n -> Expr n
renameN beta alpha = go
  where
    go : Expr n -> Expr n
    go (Var x) = Var x
    go (Lam x e) = Lam x (go e)
    go (App f e) = App (go f) (go e)
    go (Freeze gamma e) = Freeze (if gamma == beta then alpha else gamma) (go e)
    go (Mu gamma u) = Mu gamma $ if gamma == beta then u else go u

appN : MuVar -> Expr Unnamed -> Expr n -> Expr n
appN beta v = go
  where
    go : Expr n -> Expr n
    go (Var x) = Var x
    go (Lam x e) = Lam x (go e)
    go (App f e) = App (go f) (go e)
    go (Freeze alpha w) = Freeze alpha $ if alpha == beta then App (go w) v else go w
    go (Mu alpha u) = Mu alpha $ if alpha /= beta then go u else u

reduceTo : a -> Writer Any a
reduceTo x = tell (GetAny True) *> pure x

reduce0 : Expr n -> Writer Any (Expr n)
reduce0 (App (Lam x u) v) = reduceTo $ substU x v u
reduce0 (App (Mu b u) v) = reduceTo $ Mu b $ appN b v u
reduce0 (Freeze a (Mu b u)) = reduceTo $ renameN b a u
reduce0 e = pure e

reduce1 : Expr n -> Writer Any (Expr n)
reduce1 (Var x)      = pure $ Var x
reduce1 (Lam x e)    = reduce0 =<< (Lam x <$> reduce1 e)
reduce1 (App f e)    = reduce0 =<< (App <$> reduce1 f <*> reduce1 e)
reduce1 (Freeze a e) = reduce0 =<< (Freeze a <$> reduce1 e)
reduce1 (Mu a u)     = reduce0 =<< (Mu a <$> reduce1 u)

reduce : Expr n -> Expr n
reduce e = case runWriter (reduce1 e) of
    (e', GetAny changed) => if changed then assert_total $ reduce e' else e

example : Nat -> Expr Unnamed
example Z = App (App t (Var "x")) (Var "y")
  where
    t : Expr Unnamed
    t = Lam "x" $ Lam "y" $ Mu "delta" $ Freeze "phi" $ App (Var "x") (Var "y")   
example (S n) = App (example n) (Var ("z_" ++ show (S n)))      