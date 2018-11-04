module KSF.Programs

import KSF.Prelim
import KSF.Lambda

%access public export
%default total

data Pro = RetT 
         | VarT Nat Pro 
         | AppT Pro 
         | LamT Pro Pro

compile : Term -> Pro -> Pro
compile (Var n)   p = VarT n p
compile (App s t) p = compile s (compile t (AppT p))
compile (Lam s)   p = LamT (compile s RetT) p

decompile : Pro -> List Term -> Maybe (List Term)
decompile RetT       as         = Just as
decompile (VarT n p) as         = decompile p (Var n :: as)
decompile (LamT q p) as         with (decompile q [])
  | Just [s] = decompile p (Lam s :: as)
  | _        = Nothing
decompile (AppT p)   (t::s::as) = decompile p (App s t :: as)
decompile (AppT p)   _          = Nothing

decompileCorrect : (s : Term) -> (p : Pro) -> (as : List Term) -> decompile (compile s p) as = decompile p (s :: as)
decompileCorrect (Var n)   p as = Refl
decompileCorrect (App s t) p as = 
  rewrite decompileCorrect s (compile t (AppT p)) as in 
  decompileCorrect t (AppT p) (s::as)
decompileCorrect (Lam s)   p as = 
  rewrite decompileCorrect s RetT [] in 
  Refl
  
repsP : Pro -> Term -> Type
repsP p s = decompile p [] = Just [s]  

decompileAppend : (p : Pro) -> (as, as1, bs : List Term) -> decompile p as = Just as1 -> decompile p (as++bs) = Just (as1++bs)
decompileAppend RetT       as         as1 bs prf = 
  rewrite justInjective prf in Refl
decompileAppend (VarT k x) as         as1 bs prf = 
  decompileAppend x (Var k :: as) as1 bs prf
decompileAppend (AppT x)   []         as1 bs prf = absurd prf
decompileAppend (AppT x)   (_::[])    as1 bs prf = absurd prf
decompileAppend (AppT x)   (t::s::as) as1 bs prf = 
  decompileAppend x (App s t :: as) as1 bs prf
decompileAppend (LamT x y) as         as1 bs prf with (decompile x []) 
  | Just []        = absurd prf
  | Just [z]       = decompileAppend y (Lam z :: as) as1 bs prf
  | Just (_::_::_) = absurd prf
  | Nothing        = absurd prf

decompileLamTInv : (p, q : Pro) -> (as, bs : List Term) -> decompile (LamT q p) as = Just bs 
               -> (s ** (decompile q [] = Just [s], decompile p (Lam s :: as) = Just bs))
decompileLamTInv p q as bs prf with (decompile q []) 
  | Just []        = absurd prf
  | Just [s]       = (s ** (Refl, prf))
  | Just (_::_::_) = absurd prf
  | Nothing        = absurd prf

substP : Pro -> Nat -> Pro -> Pro
substP  RetT      k r = RetT
substP (VarT n p) k r with (decEq n k) 
  substP (VarT n p) n r | Yes Refl = LamT r (substP p n r)
  substP (VarT n p) k r | No _ = VarT n (substP p k r)
substP (AppT p)   k r = AppT (substP p k r)
substP (LamT q p) k r = LamT (substP q (S k) r) (substP p k r)

substPRepSubst : (q, r : Pro) -> (t : Term) -> (k : Nat) -> (as, bs : List Term) 
             -> repsP r t -> decompile q as = Just bs 
             -> decompile (substP q k r) (map (\s => subst s k (Lam t)) as) = Just (map (\s => subst s k (Lam t)) bs)
substPRepSubst  RetT      r t k as          bs rrt prf = rewrite justInjective prf in Refl
substPRepSubst (VarT n x) r t k as          bs rrt prf with (decEq n k) 
  substPRepSubst (VarT n x) r t n as bs rrt prf | Yes Refl  = 
    rewrite rrt in 
    rewrite sym $ substPRepSubst x r t n (Var n :: as) bs rrt prf in 
    rewrite decEqSelfIsYes {x=n} in
    Refl
  substPRepSubst (VarT n x) r t k as bs rrt prf | No contra = 
    rewrite sym $ substPRepSubst x r t k (Var n :: as) bs rrt prf in 
    rewrite snd $ decEqDiffIsNo contra in 
    Refl
substPRepSubst (AppT x)   r t k []          bs rrt prf = absurd prf
substPRepSubst (AppT x)   r t k [_]         bs rrt prf = absurd prf
substPRepSubst (AppT x)   r t k (a::a1::as) bs rrt prf = 
  substPRepSubst x r t k (App a1 a :: as) bs rrt prf
substPRepSubst (LamT x y) r t k as          bs rrt prf with (decompile x []) proof decx
  | Just []        = absurd prf
  | Just [s]       = rewrite substPRepSubst x r t (S k) [] [s] rrt (sym decx) in
                     substPRepSubst y r t k (Lam s :: as) bs rrt prf
  | Just (_::_::_) = absurd prf
  | Nothing        = absurd prf

data BoundP : Pro -> Nat -> Type where
  BoundPRet :                                 BoundP RetT       k
  BoundPVar : LT n k         -> BoundP p k -> BoundP (VarT n p) k
  BoundPLam : BoundP q (S k) -> BoundP p k -> BoundP (LamT q p) k
  BoundPApp : BoundP p k                   -> BoundP (AppT p)   k

closedP : Pro -> Type
closedP p = BoundP p Z  

boundCompile : BoundL s k -> BoundP p k -> BoundP (compile s p) k
boundCompile (Bndvar ltnk)  bp = BoundPVar ltnk bp
boundCompile (BndApp bs bt) bp = boundCompile bs $ boundCompile bt (BoundPApp bp) 
boundCompile (Bndlam bs)    bp = BoundPLam (boundCompile bs BoundPRet) bp
