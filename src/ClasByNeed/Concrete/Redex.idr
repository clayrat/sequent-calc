module ClasByNeed.Concrete.Redex

import Control.Monad.State
import ClasByNeed.Identifier
import ClasByNeed.List
import ClasByNeed.Concrete.Syntax
import ClasByNeed.Concrete.Substitution

%default total
%access public export

data Demanded x a = DEmpty
                  | DLet a (Command x a) x (Demanded x a)

fromEnv : Environment x a -> Demanded x a
fromEnv tau = case viewr tau of
  EmptyR                  => DEmpty
  ConsR tau' (Bind x a c) => DLet a c x (assert_total $ fromEnv tau')

fromDemand : Demanded x a -> Environment x a
fromDemand  DEmpty        = empty
fromDemand (DLet a c x d) = fromDemand d |> Bind x a c

fillDemand : Demanded x a -> Command x a -> Command x a
fillDemand  DEmpty         c' = c'
fillDemand (DLet a c1 x d) c' = C (Mu a c1) (Mut x (fillDemand d c'))

data Redex x a = Beta x (Term x a) (Term x a) (CoValue x a)
               | LetVal (Value x a) x (Command x a)
               | MuLazy a (Command x a) (CoValue x a)
               | FLetVal (Value x a) x (Force x a) (Environment x a)
               | ForceLet a (Command x a) x (Demanded x a) (Force x a)

covering
contract : (Eq a, Alternative m, MonadState (List a) m) => Redex a a -> m (Command a a)                           
contract (Beta x t u e)       = 
  do x' <- fresh
     let t' = t /// x := x'
     pure (C u (Mut x' (C t' (CoVal e))))
contract (LetVal v x c)       = c //  x := v
contract (MuLazy a c e)       = c //* a := e
contract (FLetVal v x f tau)  = 
  let c' = fillDemand (fromEnv tau) (C (Val v) (CoVal (Fce f))) in
  c' // x := v
contract (ForceLet a c x d f) = 
  let tau = fromDemand d in
  pure (C (Mu a c) (CoVal (FLet x f tau)))
