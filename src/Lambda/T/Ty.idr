module Lambda.T.Ty

%access public export
%default total

data Ty = N | Imp Ty Ty

infixr 5 ~>
(~>) : Ty -> Ty -> Ty
(~>) = Imp
