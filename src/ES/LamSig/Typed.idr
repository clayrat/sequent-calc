module ES.LamSig.Typed

import Data.List.Elem
import Iter
import Elem
import Lambda.STLC.Ty
import Lambda.STLC.Term

--%access public export
%default total

mutual
  public export
  data Tm : List Ty -> Ty -> Type where
    Var  : Tm (a::g) a
    Lam  : Tm (a::g) b -> Tm g (a~>b)
    App  : Tm g (a~>b) -> Tm g a -> Tm g b
    Clos : Tm g a -> Subs d g -> Tm d a

  public export
  data Subs : List Ty -> List Ty -> Type where
    Id    : Subs g g
    Shift : Subs (a::g) g
    Cons  : Tm g a -> Subs g d -> Subs g (a::d)
    Comp  : Subs g e -> Subs e d -> Subs g d

encodeEl : (el : Elem a g) -> Subs g (a::dropWithElem g el)
encodeEl  Here      = Id
encodeEl (There el) = Comp Shift (encodeEl el)

encode : Term g a -> Tm g a
encode (Var el)  = Clos Var (encodeEl el)
encode (Lam t)   = Lam $ encode t
encode (App t u) = App (encode t) (encode u)

isVal : Tm g a -> Bool
isVal (Lam _) = True
isVal  Var    = True
isVal  _      = False

step : Tm g a -> Maybe (Tm g a)
step (App (Lam t)     u                      ) = Just $ Clos t (Cons u Id)
step (App  t          u                      ) =
  if isVal t
    then Nothing
    else [| App (step t) (pure u) |]
step (Clos (App t u)   s                     ) = Just $ App (Clos t s) (Clos u s)
step (Clos (Lam t)     s                     ) = Just $ Lam (Clos t (Cons Var (Comp Shift s)))
step (Clos (Clos t s)  r                     ) = Just $ Clos t (Comp r s)
step (Clos  Var        Id                    ) = Just Var
step (Clos  Var       (Cons t s)             ) = Just t
step (Clos  t         (Comp s Id)            ) = Just $ Clos t s
step (Clos  t         (Comp Id Shift)        ) = Just $ Clos t Shift
step (Clos  t         (Comp (Cons u s) Shift)) = Just $ Clos t s
step (Clos  t         (Comp s (Cons u r))    ) = Just $ Clos t (Cons (Clos u s) (Comp s r))
step (Clos  t         (Comp s (Comp r q))    ) = Just $ Clos t (Comp (Comp s r) q)
step  _                                        = Nothing

stepIter : Tm g a -> Tm g a
stepIter = iter step