module ES.KSigLift

import Data.List
import Lambda.STLC.Ty
import Lambda.STLC.Term

%access public export
%default total

-- k-sigma-lift machine

mutual
  data Subst : (List Ty -> Ty -> Type) -> List Ty -> List Ty -> Type where
    Comp  : {a : List Ty -> Ty -> Type} -> Subst a g1 g2 -> Subst a g2 g3 -> Subst a g1 g3
    Cons  : {a : List Ty -> Ty -> Type} -> a g2 t -> Subst a g1 g2 -> Subst a (t::g1) g2
    Id    : {a : List Ty -> Ty -> Type} -> Subst a g g
    Lift  : {a : List Ty -> Ty -> Type} -> Subst a g1 g2 -> Subst a (t::g1) (t::g2)
    Shift : {a : List Ty -> Ty -> Type} -> Subst a g (t::g)

  data Thunk : (List Ty -> Ty -> Type) -> List Ty -> Ty -> Type where
    Th : {a : List Ty -> Ty -> Type} -> a g1 t -> Subst (Thunk a) g1 g -> Thunk a g t  

lookup : {a : List Ty -> Ty -> Type} 
      -> ({g : List Ty} -> {s : Ty} -> Elem s g -> Thunk a g s) 
      -> ({g1, g2 : List Ty} -> {t : Ty} -> Thunk a g1 t -> Subst (Thunk a) g1 g2 -> Thunk a g2 t) 
      -> Elem t g1 -> Subst (Thunk a) g1 g2 -> Thunk a g2 t
lookup box under  v        (Comp r s) = under (lookup box under v r) s
lookup _   _      Here     (Cons x _) = x
lookup box under (There v) (Cons _ s) = lookup box under v s
lookup box _      v         Id        = box v
lookup box _      Here     (Lift _)   = box Here
lookup box under (There v) (Lift s)   = under (lookup box under v s) Shift
lookup box _      v         Shift     = box (There v)    

boxvar : Elem t g -> Thunk Term g t
boxvar v = Th (Var v) Id

close : Thunk Term g1 t -> Subst (Thunk Term) g1 g2 -> Thunk Term g2 t
close (Th t r) s = Th t (Comp r s)

mutual
  subst : Term g1 t -> Subst (Thunk Term) g1 g2 -> Term g2 t
  subst (App t1 t2) s  = App (subst t1 s) (subst t2 s)
  subst (Lam t)     s  = Lam $ subst t $ Lift s
  subst (Var v)     Id = Var v
  subst (Var v)     s  = assert_total $ force $ lookup boxvar close v s

  force : Thunk Term g t -> Term g t
  force (Th t r) = subst t r

data Context : (List Ty -> Ty -> Type) -> List Ty -> List Ty -> Ty -> Ty -> Type where
  App1 : Context a g1 g2 s t -> a g1 r -> Context a g1 g2 (r~>s) t
  App2 : a g1 (r~>s) -> Context a g1 g2 s t -> Context a g1 g2 r t
  Lam1 : Context a g1 g2 (r~>s) t -> Context a (r::g1) g2 s t
  Top  : Context a g g t t

foldctx : {a : List Ty -> Ty -> Type} 
       -> ({g : List Ty} -> {r : Ty} -> a g r -> Term g r) -> Term g1 s -> Context a g1 g2 s t -> Term g2 t
foldctx f z (App1 ctx y) = foldctx f (App z (f y)) ctx
foldctx f z (App2 x ctx) = foldctx f (App (f x) z) ctx
foldctx f z (Lam1 ctx)   = foldctx f (Lam z)       ctx
foldctx _ z  Top         = z  

data Head : List Ty -> Ty -> Type where
  VH : Elem t g -> Head g t

data Spine : (a : (List Ty -> Ty -> Type) -> List Ty -> Ty -> Type) -> List Ty -> Ty -> Type where
  Sp : Head g1 s -> Context (a Term) g1 g s t -> Spine a g t

eval : Thunk Term g1 s -> Context (Thunk Term) g1 g2 s t -> Spine Thunk g2 t
eval (Th (App t1 t2) s)  ctx         = assert_total $ eval (Th t1 s) (App1 ctx (Th t2 s))
eval (Th (Lam t)   s)   (App1 ctx x) = assert_total $ eval (Th t (Cons x s)) ctx
eval (Th (Lam t)   s)    ctx         = assert_total $ eval (Th t (Lift s)) (Lam1 ctx)
eval (Th (Var v)   Id)   ctx         = Sp (VH v) ctx
eval (Th (Var v)   s)    ctx         = assert_total $ eval (lookup boxvar close v s) ctx  

data Subst1 : (a : List Ty -> Ty -> Type) -> List Ty -> List Ty -> Type where
  Comp1 : Subst a g1 g2 -> Subst1 a g2 g3 -> Subst1 a g1 g3
  Id1   : Subst1 a g g
  
data Thunk1 : (a : List Ty -> Ty -> Type) -> List Ty -> Ty -> Type where
  Th1 : a g1 t -> Subst1 (Thunk1 a) g1 g -> Thunk1 a g t
  
data Machine : List Ty -> Ty -> Type where
  M : Thunk1 Term g1 s -> Context (Thunk1 Term) g1 g s t -> Machine g t

coerce : {a : List Ty -> Ty -> Type} -> Subst1 a g1 g2 -> Subst a g1 g2
coerce (Comp1 r s) = Comp r (coerce s)
coerce  Id1        = Id  

step : Machine g t -> Either (Spine Thunk1 g t) (Machine g t)
step (M (Th1 (Var v)         (Comp1  Shift             s))                  ctx ) = Right (M (Th1 (Var (There v))                                         s   )                  ctx )
step (M (Th1 (Var Here)      (Comp1 (Cons (Th1 u p) _) s))                  ctx ) = Right (M (Th1  u              (Comp1 (coerce p)                       s  ))                  ctx )
step (M (Th1 (Var Here)      (Comp1 (Lift _)           s))                  ctx ) = Right (M (Th1 (Var Here)                                              s   )                  ctx )
step (M (Th1 (Var (There v)) (Comp1 (Cons (Th1 _ _) r) s))                  ctx ) = Right (M (Th1 (Var v)         (Comp1  r                               s  ))                  ctx )
step (M (Th1 (Var (There v)) (Comp1 (Lift r)           s))                  ctx ) = Right (M (Th1 (Var v)         (Comp1  r                  (Comp1 Shift s) ))                  ctx )
step (M (Th1 t               (Comp1 (Comp p r)         s))                  ctx ) = Right (M (Th1  t              (Comp1  p                  (Comp1 r     s) ))                  ctx )
step (M (Th1 t               (Comp1  Id                s))                  ctx ) = Right (M (Th1  t                                                      s   )                  ctx )
step (M (Th1 t                s                          ) (App2 (Th1 s1 r) ctx)) = Right (M (Th1  s1                                                     r   )  (App1 ctx (Th1 t s)))
step (M (Th1 (App s0 (Var v)) s                          )                  ctx ) = Right (M (Th1 (Var v)                                                 s   ) (App2 (Th1 s0 s) ctx))
step (M (Th1 (App s0 t)       s                          )                  ctx ) = Right (M (Th1  s0                                                     s   )  (App1 ctx (Th1 t s)))
step (M (Th1 (Lam t)          s                          )          (App1 ctx x)) = Right (M (Th1  t              (Comp1 (Cons x (coerce s))              Id1))                  ctx )
step (M (Th1 (Lam t)          s                          )                  ctx ) = Right (M (Th1  t              (Comp1 (Lift (coerce s))                Id1))            (Lam1 ctx))
step (M (Th1 (Var v)          Id1                        )                   ctx) = Left (Sp (VH v) ctx)

stepIter : Machine g t -> Spine Thunk1 g t
stepIter m = case step m of 
  Left x => x    
  Right m1 => assert_total $ stepIter m1

runKSL : Term g a -> Spine Thunk1 g a  
runKSL t = stepIter $ M (Th1 t Id1) Top
