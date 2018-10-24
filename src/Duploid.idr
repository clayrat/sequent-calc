module Duploid

-- port of https://github.com/freebroccolo/agda-syntactic-duploids/blob/master/src/Duploid.agda

%default total
%access public export

data Pol = Plus | Minus
  
data Dir = L | R

data Sco : Dir -> Type where
  NS : Sco d
  CS : Sco d -> Pol -> Sco d

data Var' : Pol -> Sco d -> Type where
  NV : Var' p (CS s p)
  SV : Var' p s -> Var' p (CS s q)  

Var : Sco d -> Pol -> Type
Var {d} s p = Var' {d} p s  

mutual
  record Cmd (g : Sco L) (d : Sco R) where
    constructor MkCmd
    {pol : Pol}
    exp : Exp g d pol
    ctx : Ctx g d pol

  data Exp : Sco L -> Sco R -> Pol -> Type where
    VarE   : Var g Minus -> Exp g d Minus
    MuE    : Cmd g (CS d p) -> Exp g d p
    MuPatE : Cmd g (CS d Plus) -> Exp g d Minus
    UpE    : Val g d Plus -> Exp g d Plus

  data Val : Sco L -> Sco R -> Pol -> Type where
    VarV  : Var g Plus -> Val g d Plus
    WrapV : Exp g d Minus -> Val g d Plus
    DownV : Exp g d p -> Val g d p

  data Ctx : Sco L -> Sco R -> Pol -> Type where
    VarC   : Var d Plus -> Ctx g d Plus
    NuC    : Cmd (CS g p) d -> Ctx g d p
    NuPatC : Cmd (CS g Minus) d -> Ctx g d Plus
    UpC    : Stk g d Minus -> Ctx g d Minus

  data Stk : Sco L -> Sco R -> Pol -> Type where
    VarS  : Var d Minus -> Stk g d Minus
    WrapS : Ctx g d Plus -> Stk g d Minus
    DownS : Ctx g d Plus -> Stk g d Plus

data Lt : Sco d -> Sco d -> Type where
  I   : Lt s s
  LUP : Lt s0 s1 -> Lt (CS s0 p) s1
  LEX : Lt s0 s1 -> Lt (CS s0 p) (CS s1 p)
  LAD : Lt s0 s1 -> Lt (CS (CS s0 p0) p1) (CS (CS s1 p1) p0)

Gt : Sco d -> Sco d -> Type 
Gt s1 s0 = Lt s0 s1

gtVar : Gt s0 s1 -> Var s0 p -> Var s1 p
gtVar  I       x          = x
gtVar (LUP r)  x          = SV (gtVar r x)
gtVar (LEX r)  NV         = NV
gtVar (LEX r) (SV x)      = SV (gtVar r x)
gtVar (LAD r)  NV         = SV NV
gtVar (LAD r) (SV NV)     = NV
gtVar (LAD r) (SV (SV x)) = SV (SV (gtVar r x))

mutual
  gtCmd : {auto p0 : Gt g0 g1} -> {auto p1 : Gt d0 d1} -> Cmd g0 d0 -> Cmd g1 d1
  gtCmd {p0} {p1} (MkCmd v e) = MkCmd (gtExp {p0} {p1} v) (gtCtx {p0} {p1} e)

  gtExp : {auto p0 : Gt g0 g1} -> {auto p1 : Gt d0 d1} -> Exp g0 d0 p -> Exp g1 d1 p
  gtExp {p0}      (VarE xm)  = VarE (gtVar p0 xm)
  gtExp {p0} {p1} (MuE c)    = MuE (gtCmd {p0} {p1=LEX p1} c)
  gtExp {p0} {p1} (MuPatE c) = MuPatE (gtCmd {p0} {p1=LEX p1} c)
  gtExp {p0} {p1} (UpE wp)   = UpE (gtVal {p0} {p1} wp)

  gtVal : {auto p0 : Gt g0 g1} -> {auto p1 : Gt d0 d1} -> Val g0 d0 p -> Val g1 d1 p
  gtVal {p0}      (VarV xp)  = VarV (gtVar p0 xp)
  gtVal {p0} {p1} (WrapV vm) = WrapV (gtExp {p0} {p1} vm)
  gtVal {p0} {p1} (DownV vm) = DownV (gtExp {p0} {p1} vm)

  gtCtx : {auto p0 : Gt g0 g1} -> {auto p1 : Gt d0 d1} -> Ctx g0 d0 p -> Ctx g1 d1 p
  gtCtx      {p1} (VarC ap)  = VarC (gtVar p1 ap)
  gtCtx {p0} {p1} (NuC c)    = NuC (gtCmd {p0=LEX p0} {p1} c)
  gtCtx {p0} {p1} (NuPatC c) = NuPatC (gtCmd {p0=LEX p0} {p1} c)
  gtCtx {p0} {p1} (UpC pi)   = UpC (gtStk {p0} {p1} pi)

  gtStk : {auto p0 : Gt g0 g1} -> {auto p1 : Gt d0 d1} -> Stk g0 d0 p -> Stk g1 d1 p
  gtStk      {p1} (VarS am)  = VarS (gtVar p1 am) 
  gtStk {p0} {p1} (WrapS ep) = WrapS (gtCtx {p0} {p1} ep)
  gtStk {p0} {p1} (DownS ep) = DownS (gtCtx {p0} {p1} ep)

mutual
  cmdExp : Cmd (CS g Minus) d -> Exp g d Minus -> Cmd g d
  cmdExp (MkCmd {pol} v e) v' = assert_total $ MkCmd (expExp v v') (ctxExp e v')

  cmdVal : Cmd (CS g Plus) d -> Val g d Plus -> Cmd g d
  cmdVal (MkCmd {pol} v e) w' = assert_total $ MkCmd (expVal v w') (ctxVal e w')

  cmdCtx : Cmd g (CS d Plus) -> Ctx g d Plus -> Cmd g d
  cmdCtx (MkCmd {pol} v e) e' = assert_total $ MkCmd (expCtx v e') (ctxCtx e e')

  cmdStk : Cmd g (CS d Minus) -> Stk g d Minus -> Cmd g d
  cmdStk (MkCmd {pol} v e) pi' = assert_total $ MkCmd (expStk v pi') (ctxStk e pi') 

  expExp : Exp (CS g Minus) d p -> Exp g d Minus -> Exp g d p
  expExp (VarE NV)      v' = v'
  expExp (VarE (SV xm)) _  = VarE xm
  expExp (MuE c)        v' = MuE (cmdExp c (gtExp v'))
  expExp (MuPatE c)     v' = MuPatE (cmdExp c (gtExp v'))
  expExp (UpE wp)       v' = UpE (valExp wp v')

  expVal : Exp (CS g Plus) d p -> Val g d Plus -> Exp g d p
  expVal (VarE (SV xm)) _  = VarE xm
  expVal (MuE c)        w' = MuE (cmdVal c (gtVal w'))
  expVal (MuPatE c)     w' = MuPatE (cmdVal c (gtVal w'))
  expVal (UpE wp)       w' = UpE (valVal wp w')
  
  expCtx : Exp g (CS d Plus) p -> Ctx g d Plus -> Exp g d p
  expCtx (VarE xm)  _  = VarE xm
  expCtx (MuE c)    e' = MuE (cmdCtx (gtCmd c) (gtCtx e'))
  expCtx (MuPatE c) e' = MuPatE (cmdCtx c (gtCtx e'))
  expCtx (UpE wp)   e' = UpE (valCtx wp e')

  expStk : Exp g (CS d Minus) p -> Stk g d Minus -> Exp g d p
  expStk (VarE xm)  _   = VarE xm
  expStk (MuE c)    pi' = MuE (cmdStk (gtCmd c) (gtStk pi'))
  expStk (MuPatE c) pi' = MuPatE (cmdStk (gtCmd c) (gtStk pi'))
  expStk (UpE wp)   pi' = UpE (valStk wp pi')

  valExp : Val (CS g Minus) d p -> Exp g d Minus -> Val g d p
  valExp (VarV (SV xp)) _  = VarV xp
  valExp (WrapV vm)     v' = WrapV (expExp vm v')
  valExp (DownV vm)     v' = DownV (expExp vm v')

  valVal : Val (CS g Plus) d p -> Val g d Plus -> Val g d p
  valVal (VarV NV)      w' = w'
  valVal (VarV (SV xp)) _  = VarV xp
  valVal (WrapV vm)     w' = WrapV (expVal vm w')
  valVal (DownV vm)     w' = DownV (expVal vm w')

  valCtx : Val g (CS d Plus) p -> Ctx g d Plus -> Val g d p
  valCtx (VarV xp)  _   = VarV xp
  valCtx (WrapV vm) pi' = WrapV (expCtx vm pi')
  valCtx (DownV vm) pi' = DownV (expCtx vm pi')

  valStk : Val g (CS d Minus) p -> Stk g d Minus -> Val g d p
  valStk (VarV xp)  _  = VarV xp
  valStk (WrapV vm) e' = WrapV (expStk vm e')
  valStk (DownV vm) e' = DownV (expStk vm e')

  ctxExp : Ctx (CS g Minus) d p -> Exp g d Minus -> Ctx g d p
  ctxExp (VarC ap)  _  = VarC ap
  ctxExp (NuC c)    v' = NuC (cmdExp (gtCmd c) (gtExp v'))
  ctxExp (NuPatC c) v' = NuPatC (cmdExp c (gtExp v'))
  ctxExp (UpC pi)   v' = UpC (stkExp pi v')

  ctxVal : Ctx (CS g Plus) d p -> Val g d Plus -> Ctx g d p
  ctxVal (VarC ap)  _  = VarC ap
  ctxVal (NuC c)    w' = NuC (cmdVal (gtCmd c) (gtVal w'))
  ctxVal (NuPatC c) w' = NuPatC (cmdVal (gtCmd c) (gtVal w'))
  ctxVal (UpC pi)   w' = UpC (stkVal pi w')

  ctxCtx : Ctx g (CS d Plus) p -> Ctx g d Plus -> Ctx g d p
  ctxCtx (VarC NV)      e' = e'
  ctxCtx (VarC (SV ap)) _  = VarC ap
  ctxCtx (NuC c)        e' = NuC (cmdCtx c (gtCtx e'))
  ctxCtx (NuPatC c)     e' = NuPatC (cmdCtx c (gtCtx e'))
  ctxCtx (UpC pi)       e' = UpC (stkCtx pi e')

  ctxStk : Ctx g (CS d Minus) p -> Stk g d Minus -> Ctx g d p
  ctxStk (VarC (SV ap)) _   = VarC ap
  ctxStk (NuC c)        pi' = NuC (cmdStk c (gtStk pi'))
  ctxStk (NuPatC c)     pi' = NuPatC (cmdStk c (gtStk pi'))
  ctxStk (UpC pi)       pi' = UpC (stkStk pi pi')

  stkExp : Stk (CS g Minus) d p -> Exp g d Minus -> Stk g d p
  stkExp (VarS am)  _  = VarS am
  stkExp (WrapS ep) v' = WrapS (ctxExp ep v')
  stkExp (DownS ep) v' = DownS (ctxExp ep v')

  stkVal : Stk (CS g Plus) d p -> Val g d Plus -> Stk g d p
  stkVal (VarS am)  _  = VarS am
  stkVal (WrapS ep) w' = WrapS (ctxVal ep w')
  stkVal (DownS ep) w' = DownS (ctxVal ep w')

  stkCtx : Stk g (CS d Plus) p -> Ctx g d Plus -> Stk g d p
  stkCtx (VarS (SV am)) _  = VarS am
  stkCtx (WrapS ep)     e' = WrapS (ctxCtx ep e')
  stkCtx (DownS ep)     e' = DownS (ctxCtx ep e')

  stkStk : Stk g (CS d Minus) p -> Stk g d Minus -> Stk g d p
  stkStk (VarS NV)      pi' = pi'
  stkStk (VarS (SV am)) _   = VarS am
  stkStk (WrapS ep)     pi' = WrapS (ctxStk ep pi')
  stkStk (DownS ep)     pi' = DownS (ctxStk ep pi')

expVar : Var g p -> Exp g d p  
expVar {p=Minus} x = VarE x
expVar {p=Plus}  x = UpE $ VarV x

ctxVar : Var d p -> Ctx g d p  
ctxVar {p=Minus} x = UpC $ VarS x
ctxVar {p=Plus}  x = VarC x

reduce : Cmd g d -> Maybe (Cmd g d)
reduce (MkCmd (MuE c)          (UpC pi))         = Just (cmdStk c pi)
reduce (MkCmd (UpE wp)         (NuC c))          = Just (cmdVal c wp)
reduce (MkCmd (UpE (WrapV vm)) (NuPatC c))       = Just (cmdExp c vm)
reduce (MkCmd (MuPatE c)       (UpC (WrapS ep))) = Just (cmdCtx c ep)
reduce _                                         = Nothing

reduceIter : Cmd g d -> Maybe (Cmd g d)
reduceIter c with (reduce c)
  | Nothing = Just c
  | Just c' = assert_total $ reduceIter c'

expandMu : Exp g d p -> Exp g d p
expandMu v = MuE (MkCmd (gtExp v) (ctxVar NV))

expandNu : Ctx g d p -> Ctx g d p
expandNu e = NuC (MkCmd (expVar NV) (gtCtx e))

expandNuPat : Ctx g d Plus -> Ctx g d Plus
expandNuPat ep = NuPatC (MkCmd (UpE (WrapV (VarE NV))) (gtCtx ep))

expandMuPat : Exp g d Minus -> Exp g d Minus
expandMuPat vm = MuPatE (MkCmd (gtExp vm) (UpC (WrapS (VarC NV))))

letE : Exp g d Plus -> Exp (CS g Minus) d p -> Exp g d p
letE v0p v1 = MuE (MkCmd (gtExp v0p) (NuPatC (MkCmd (gtExp v1) (ctxVar NV))))

delay : Val g d Plus -> Exp g d Minus
delay wp = MuPatE (MkCmd (gtExp $ UpE wp) (VarC NV))

force : Exp g d Minus -> Val g d Plus 
force vm = DownV (MuE (MkCmd (gtExp vm) (UpC (WrapS (VarC NV)))))

wrap : Exp g d Minus -> Val g d Plus
wrap = WrapV

unwrap : Val g d Plus -> Exp g d Minus
unwrap wp = letE (UpE wp) (VarE NV)