module FB

-- port of https://github.com/freebroccolo/sequent-calculus/blob/master/src/Calculus.agda

%default total
%access public export

data Pol = Pos | Neg

neg : Pol -> Pol
neg Pos = Neg
neg Neg = Pos

data Side = LH | RH

Var : Side -> Nat -> Nat -> Type
Var LH = LT
Var RH = GT

-- untyped

mutual
  data Cmd : (m, n, o, p : Nat) -> Type where
    MkCmd : Exp m n o p pol -> Ctx m n o p pol -> Cmd m n o p

  data Val : (m, n, o, p : Nat) -> Type where
    VarV : Var RH m n                 -> Val m n o p
    D    : Exp m n o p Neg            -> Val m n o p
    NotV : Stack m n o p              -> Val m n o p
    I0   : Val m n o p                -> Val m n o p
    I1   : Val m n o p                -> Val m n o p
    Ten  : Val m n o p -> Val m n o p -> Val m n o p

  data Stack : (m, n, o, p : Nat) -> Type where
    VarS : Var LH o p                     -> Stack m n o p
    U    : Ctx m n o p Pos                -> Stack m n o p
    NotS : Val m n o p                    -> Stack m n o p
    P0   : Stack m n o p                  -> Stack m n o p
    P1   : Stack m n o p                  -> Stack m n o p
    Par  : Stack m n o p -> Stack m n o p -> Stack m n o p

  data Exp : (m, n, o, p : Nat) -> Pol -> Type where
    VarE  : Var RH m n                         -> Exp m n o p Neg
    MuU   : Cmd m n o (S p)                    -> Exp m n o p Neg
    MuNot : Cmd (S m) n o p                    -> Exp m n o p Neg
    Mu    : Cmd m n o (S p)                    -> Exp m n o p pol
    MuPar : Cmd m n o (S (S p))                -> Exp m n o p Neg
    MuCpa : Cmd m n o (S p) -> Cmd m n o (S p) -> Exp m n o p Neg
    QE    : Val m n o p                        -> Exp m n o p Pos

  data Ctx : (m, n, o, p : Nat) -> Pol -> Type where
    VarC  : Var LH o p                         -> Ctx m n o p Pos
    NuD   : Cmd (S m) n o p                    -> Ctx m n o p Pos
    NuNot : Cmd m n o (S p)                    -> Ctx m n o p Pos
    Nu    : Cmd (S m) n o p                    -> Ctx m n o p pol
    NuTen : Cmd (S (S m)) n o p                -> Ctx m n o p Pos
    NuCpr : Cmd (S m) n o p -> Cmd (S m) n o p -> Ctx m n o p Pos
    QC    : Stack m n o p                      -> Ctx m n o p Neg

-- typed

data Tp : Pol -> Type where
  TpQ   : Nat              -> Tp pol
  TpTen : Tp Pos -> Tp Pos -> Tp Pos
  TpCpr : Tp Pos -> Tp Pos -> Tp Pos
  TpD   : Tp Neg           -> Tp Pos
  TpPar : Tp Neg -> Tp Neg -> Tp Neg
  TpCpa : Tp Neg -> Tp Neg -> Tp Neg
  TpU   : Tp Pos           -> Tp Neg
  TpNot : Tp pol           -> Tp (neg pol)

impV : Tp Pos -> Tp Pos -> Tp Pos
impV p q = TpD (TpNot p `TpPar` TpU q)

impN : Tp Neg -> Tp Neg -> Tp Neg
impN m n = TpU (TpNot (m `TpPar` n))

mutual
  data Tel : Side -> Nat -> Nat -> Type where
    ZT : Tel s m m
    CT : (s : Side) -> lhs s pol m n -> rhs s pol m n -> Tel s (plu s RH m) (plu s LH n)

  lhs : Side -> Pol -> Nat -> Nat -> Type
  lhs LH pol m n = Tp pol
  lhs RH pol m n = Tel RH m n

  rhs : Side -> Pol -> Nat -> Nat -> Type
  rhs LH pol m n = Tel LH m n
  rhs RH pol m n = Tp pol

  plu : Side -> Side -> Nat -> Nat
  plu LH LH i = S i
  plu RH LH i =   i
  plu LH RH i =   i
  plu RH RH i = S i

mutual
  data CmdT : (c : Cmd m n o p) -> (g : Tel RH m n) -> (d : Tel LH o p) -> Type where
    MkCmdT : ExpT g v a d -> CtxT g e a d -> CmdT (MkCmd v e) g d

  data ValT : (g : Tel RH m n) -> (vp : Val m n o p) -> (tp : Tp Pos) -> (d : Tel LH o p) -> Type where
    VarVT : (xp : Var RH (S m) n)                -> ValT (CT RH g tp) (VarV xp)     tp              d
    DT    : ExpT g v a d                         -> ValT g            (D v)         (TpD a)         d
    NotVT : StackT g e a d                       -> ValT g            (NotV e)      (TpNot a)       d
    I0T   : ValT g vp0 tp0 d                     -> ValT g            (I0 vp0)      (TpCpr tp0 tp1) d
    I1T   : ValT g vp1 tp1 d                     -> ValT g            (I1 vp1)      (TpCpr tp0 tp1) d
    TenT  : ValT g vp0 tp0 d -> ValT g vp1 tp1 d -> ValT g            (Ten vp0 vp1) (TpTen tp0 tp1) d

  data StackT : (g : Tel RH m n) -> (en : Stack m n o p) -> (tn : Tp Neg) -> (d : Tel LH o p) -> Type where
    VarST : (an : Var LH o (S p))                    -> StackT g (VarS an)     tn              (CT LH tn d)
    UT    : CtxT g e a d                             -> StackT g (U e)         (TpU a)         d
    NotST : ValT g v a d                             -> StackT g (NotS e)      (TpNot a)       d
    P0T   : StackT g en0 tn0 d                       -> StackT g (P0 en0)      (TpCpa tn0 tn1) d
    P1T   : StackT g en1 tn1 d                       -> StackT g (P1 en1)      (TpCpa tn0 tn1) d
    ParT  : StackT g en0 tn0 d -> StackT g en1 tn1 d -> StackT g (Par en0 en1) (TpPar tn0 tn1) d

  data ExpT : (g : Tel RH m n) -> (v : Exp m n o p pol) -> (a : Tp pol) -> (d : Tel LH o p) -> Type where
    VarET  : (xn : Var RH (S m) n)                              -> ExpT (CT RH g tp) (VarE xn)     tp                   d
    MuUT   : CmdT c g (CT LH tp d)                              -> ExpT g            (MuU c)       (TpU tp)             d
    MuNotT : CmdT c (CT RH g tp) d                              -> ExpT g            (MuNot c)     (TpNot {pol=Pos} tp) d
    MuT    : CmdT c g (CT LH t d)                               -> ExpT g            (Mu c)        t                    d
    MuParT : CmdT c g (CT LH tn0 (CT LH tn1 d))                 -> ExpT g            (MuPar c)     (TpPar tn0 tn1)      d
    MuCpaT : CmdT c0 g (CT LH tn0 d) -> CmdT c1 g (CT LH tn1 d) -> ExpT g            (MuCpa c0 c1) (TpCpa tn0 tn1)      d
    QET    : ValT g v tp d                                      -> ExpT g            (QE v)        tp                   d

  data CtxT : (g : Tel RH m n) -> (e : Ctx m n o p pol) -> (a : Tp pol) -> (d : Tel LH o p) -> Type where
    VCT    : (ap : Var LH o (S p))                              -> CtxT g (VarC ap)     tp                   (CT LH tp d)
    NuDT   : CmdT c (CT RH g tn) d                              -> CtxT g (NuD c)       (TpD tn)             d
    NuNotT : CmdT c g (CT LH tn d)                              -> CtxT g (NuNot c)     (TpNot {pol=Neg} tn) d
    NuT    : CmdT с (CT RH g t) d                               -> CtxT g (Nu c)        t                    d
    NuTenT : CmdT c (CT RH (CT RH g tp0) tp1) d                 -> CtxT g (NuTen c)     (TpTen tp0 tp1)      d
    NuCprT : CmdT с0 (CT RH g tp0) d -> CmdT с1 (CT RH g tp1) d -> CtxT g (NuCpr c0 c1) (TpCpr tp0 tp1)      d
    QCT    : StackT g e tn d                                    -> CtxT g (QC e)        tn                   d
