module Lambda.T.Iter.Ty

%access public export
%default total

data Ty = N | Imp Ty Ty | Prod Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp
