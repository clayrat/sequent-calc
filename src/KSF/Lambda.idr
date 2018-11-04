module KSF.Lambda

import KSF.Prelim

%access public export
%default total

%hide Language.Reflection.Var
%hide Language.Reflection.App
%hide Language.Reflection.Lam

data Term : Type where
  Var : Nat -> Term
  App : Term -> Term -> Term
  Lam : Term -> Term

Uninhabited (Var _ = App _ _) where
  uninhabited Refl impossible

Uninhabited (App _ _ = Var _) where
  uninhabited Refl impossible

Uninhabited (Var _ = Lam _) where
  uninhabited Refl impossible

Uninhabited (Lam _ = Var _) where
  uninhabited Refl impossible

Uninhabited (App _ _ = Lam _) where
  uninhabited Refl impossible

Uninhabited (Lam _ = App _ _) where
  uninhabited Refl impossible

varInj : Var x = Var y -> x = y
varInj Refl = Refl

appInj : App x y = App s t -> (x = s, y = t)
appInj Refl = (Refl, Refl)

lamInj : Lam x = Lam y -> x = y
lamInj Refl = Refl

DecEq Term where
  decEq (Var k)   (Var j) with (decEq k j) 
    decEq (Var k) (Var k) | Yes Refl = Yes Refl
    decEq (Var k) (Var j) | No contra = No $ contra . varInj
  decEq (Var _)   (App _ _) = No absurd
  decEq (Var _)   (Lam _)   = No absurd
  decEq (App _ _) (Var _)   = No absurd
  decEq (App x y) (App s t) with (decEq x s) 
    decEq (App x y) (App x t) | Yes Refl with (decEq y t) 
      decEq (App x y) (App x y) | Yes Refl | Yes Refl = Yes Refl
      decEq (App x y) (App x t) | Yes Refl | No contra = No $ contra . snd . appInj
    decEq (App x y) (App s t) | No contra = No $ contra . fst . appInj
  decEq (App _ _) (Lam _)   = No absurd
  decEq (Lam _)   (Var _)   = No absurd
  decEq (Lam _)   (App _ _) = No absurd
  decEq (Lam x)   (Lam y) with (decEq x y) 
    decEq (Lam x)   (Lam x) | Yes Refl = Yes Refl
    decEq (Lam x)   (Lam y) | No contra = No $ contra . lamInj

data Abstraction : Term -> Type where
  IsAbstraction : (s : Term) -> Abstraction (Lam s)

Uninhabited (Abstraction (App _ _)) where
  uninhabited (IsAbstraction _) impossible  

Uninhabited (Abstraction (Var _)) where
  uninhabited (IsAbstraction _) impossible  

{-
decAbstraction : (x : Term) -> Dec (Abstraction x)
decAbstraction (Var n)   = No absurd
decAbstraction (App s t) = No absurd
decAbstraction (Lam s)   = Yes (IsAbstraction s)   
-}

-- substitution

subst : Term -> Nat -> Term -> Term
subst (Var n)   k u with (decEq n k) 
  subst (Var n)   n u | Yes Refl = u
  subst (Var n)   k u | No _     = Var n
subst (App s t) k u = App (subst s k u) (subst t k u)
subst (Lam s)   k u = Lam (subst s (S k) u)

-- reduction

data StepL : Term -> Term -> Type where
  StepLApp  : y = subst s Z (Lam t) -> StepL (App (Lam s) (Lam t)) y
  StepLAppR : StepL t t'            -> StepL (App (Lam s) t)       (App (Lam s) t')
  StepLAppL : StepL s s'            -> StepL (App s t)             (App s' t)

Uninhabited (StepL (Var _) _) where
  uninhabited StepLApp impossible  
  uninhabited (StepLAppR _) impossible  
  uninhabited (StepLAppL _) impossible  

Uninhabited (StepL (Lam _) _) where
  uninhabited StepLApp impossible  
  uninhabited (StepLAppR _) impossible  
  uninhabited (StepLAppL _) impossible

ARS Term where
  ARS_R = StepL

stepLFunct : functional StepL 
stepLFunct (App (Lam s) (Lam t))  y                     z              (StepLApp ys)     (StepLApp zs)    = rewrite ys in rewrite zs in Refl
stepLFunct (App (Lam s) (Lam t)) (App (Lam s) (Lam q))  z              (StepLAppR stq)   (StepLApp zs)    = absurd stq
stepLFunct (App (Lam s) t)       (App (Lam s) q)       (App (Lam s) u) (StepLAppR stq)   (StepLAppR stu)  = cong $ stepLFunct t q u stq stu
stepLFunct (App (Lam s) t)       (App (Lam s) q)       (App u t)       (StepLAppR stq)   (StepLAppL slsu) = absurd slsu
stepLFunct (App (Lam s) (Lam r)) (App (Lam u) (Lam r))  z              (StepLAppL slslu) (StepLApp zs)    = absurd slslu
stepLFunct (App (Lam s) t)       (App (Lam u) t)       (App (Lam s) q) (StepLAppL slslu) (StepLAppR stq)  = absurd slslu
stepLFunct (App s r)             (App t r)             (App u r)       (StepLAppL sst)   (StepLAppL ssu)  = cong {f=\z=>App z r} $ stepLFunct s t u sst ssu
  
redL : Term -> Maybe Term
redL (App (Lam s) (Lam t)) = Just (subst s Z (Lam t))
redL (App (Lam s) t)       = do t' <- redL t
                                pure (App (Lam s) t')
redL (App s t)             = do s' <- redL s 
                                pure (App s' t)
redL _                     = Nothing

stepLComputable : stepFunction StepL Lambda.redL
stepLComputable (Var n)                 = \_ => absurd 
stepLComputable (App (Var k) t)         = \y, savkt => case savkt of 
  StepLAppL svk => absurd svk
stepLComputable (App (App x y) t)       = aux (stepLComputable (App x y))
  where
  aux : stepFunctionAux StepL (App x y) (redL (App x y)) 
     -> stepFunctionAux StepL (App (App x y) t) ((redL (App x y)) >>= (\s' => Just (App s' t)))
  aux sa with (redL (App x y))
    aux sa | Just _  = StepLAppL sa
    aux sa | Nothing = \y, saa => case saa of 
      StepLAppL {s'=q} saq => absurd $ sa q saq
stepLComputable (App (Lam x) (Var k))   = \y, salxvk => case salxvk of 
  StepLAppL slx => absurd slx
stepLComputable (App (Lam x) (App y z)) = aux (stepLComputable (App y z))
where
  aux : stepFunctionAux StepL (App y z) (redL (App y z)) 
     -> stepFunctionAux StepL (App (Lam x) (App y z)) ((redL (App y z)) >>= (\t' => Just (App (Lam x) t')))
  aux sa with (redL (App y z))
    aux sa | Just _  = StepLAppR sa
    aux sa | Nothing = \y, saa => case saa of 
      StepLAppR {t'=q} saq => absurd $ sa q saq
      StepLAppL slx => absurd slx
stepLComputable (App (Lam x) (Lam y))   = StepLApp Refl
stepLComputable (Lam s)                 = \_ => absurd

-- bound and closedness for terms

data BoundL : Term -> Nat -> Type where
  Bndvar : LT n k -> BoundL (Var n) k
  BndApp : BoundL s k -> BoundL t k -> BoundL (App s t) k
  Bndlam : BoundL s (S k) -> BoundL (Lam s) k

closedL : Term -> Type
closedL s = BoundL s Z

-- stuck terms

data Stuck : Term -> Type where
  StuckVar : Stuck (Var x)
  StuckL   : Stuck s -> Stuck (App s t)
  StuckR   : Stuck t -> Stuck (App (Lam s) t)

Uninhabited (Stuck (Lam _)) where
  uninhabited StuckVar impossible  
  uninhabited (StuckL _) impossible  
  uninhabited (StuckR _) impossible

notAbsLNotReducible : Not (reducible StepL x) -> Not (Abstraction x) -> Not (reducible StepL (App x y))
notAbsLNotReducible _   nax (_ ** StepLApp {s} _)          = nax $ IsAbstraction s
notAbsLNotReducible _   nax (App (Lam s) _ ** StepLAppR _) = nax $ IsAbstraction s
notAbsLNotReducible nrx _   (App s _ ** StepLAppL sxs)     = nrx (s ** sxs)

notAbsRNotReducible : Not (reducible StepL x) -> Not (reducible StepL y) -> Not (Abstraction y) -> Not (reducible StepL (App x y))
notAbsRNotReducible _   _   nay (_ ** StepLApp {t} _)            = nay $ IsAbstraction t
notAbsRNotReducible _   nry _   (App (Lam _) t ** StepLAppR syt) = nry (t ** syt)
notAbsRNotReducible nrx _   _   (App s _ ** StepLAppL sxs)       = nrx (s ** sxs)

notStuckL : Not (Stuck x) -> StepL x x1 -> Not (Stuck (App x y))
notStuckL nsx _ (StuckL sl) = nsx sl
notStuckL nsx sxx1 (StuckR sr) = absurd sxx1

notStuckLR : Not (Stuck x) -> Not (Stuck y) -> Not (Stuck (App x y))
notStuckLR nsx nsy (StuckL sl) = nsx sl
notStuckLR nsx nsy (StuckR sr) = nsy sr

LTrichotomy : (s : Term) -> exactlyOneHolds [reducible StepL s, Abstraction s, Stuck s]  
LTrichotomy (Var k)   = Right (\(_**s) => absurd s, Right (absurd, Left (StuckVar, ())))
LTrichotomy (App x y) = 
  case LTrichotomy x of 
    Left ((x1 ** sxx1), _, nsx, ()) => 
      Left ((App x1 y ** StepLAppL sxx1), absurd, notStuckL nsx sxx1, ())
    Right (nrx, Left (IsAbstraction lx, nsx, ())) => 
      case LTrichotomy y of 
        Left ((y1 ** syy1), nay, nsy, ()) => 
          Left ((App (Lam lx) y1 ** StepLAppR syy1), absurd, notStuckLR nsx nsy, ())
        Right (nry, Left (IsAbstraction ly, nsy, ())) =>
          Left ((subst lx Z (Lam ly) ** StepLApp Refl), absurd, notStuckLR nsx nsy, ())
        Right (nry, Right (nay, Left (sy, ()))) => 
          Right (notAbsRNotReducible nrx nry nay, Right (absurd, Left (StuckR sy, ())))
        Right (nry, Right (nay, Right (_, v))) => absurd v
    Right (nrx, Right (nax, Left (sx, ()))) => 
      Right (notAbsLNotReducible nrx nax, Right (absurd, Left (StuckL sx, ())))
    Right (nrx, Right (nax, Right (_, v))) => absurd v
LTrichotomy (Lam x)   = Right (\(_**s) => absurd s, Left (IsAbstraction x, absurd, ()))
