module Lambda.Ty

%access public export
%default total

data Ty = A | Imp Ty Ty
