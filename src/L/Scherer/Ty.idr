module L.Scherer.Ty

%access public export
%default total

data Ty = A | Imp Ty Ty
