module Lambda.PCFV.Mod.Ty

%default total

public export
data Ty = A | Imp Ty Ty | C Ty

infixr 5 ~>
public export
(~>) : Ty -> Ty -> Ty
(~>) = Imp