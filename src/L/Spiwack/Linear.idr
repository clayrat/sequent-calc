module L.Linear

%access public export
%default total

data Ty = AL | AR 
        | Ten Ty Ty | Par  Ty Ty | One  | Bot
        | Sum Ty Ty | With Ty Ty | Zero | Top  
        | ExpL Ty | ExpR Ty

dual : Ty -> Ty
dual  AL          = AR
dual  AR          = AL
dual (Ten  t1 t2) = Par (dual t1) (dual t2)
dual (Par  t1 t2) = Ten (dual t1) (dual t2)
dual  One         = Bot
dual  Bot         = One
dual (Sum  t1 t2) = With (dual t1) (dual t2)
dual (With t1 t2) = Sum (dual t1) (dual t2)
dual  Zero        = Top
dual  Top         = Zero
dual (ExpL t)     = ExpR (dual t)
dual (ExpR t)     = ExpL (dual t)

dualInv : dual (dual a) = a
dualInv {a=AL}       = Refl
dualInv {a=AR}       = Refl
dualInv {a=Ten a b}  = 
  rewrite dualInv {a} in 
  rewrite dualInv {a=b} in 
  Refl
dualInv {a=Par a b}  = 
  rewrite dualInv {a} in 
  rewrite dualInv {a=b} in 
  Refl
dualInv {a=One}      = Refl
dualInv {a=Bot}      = Refl
dualInv {a=Sum a b}  = 
  rewrite dualInv {a} in 
  rewrite dualInv {a=b} in 
  Refl
dualInv {a=With a b} = 
  rewrite dualInv {a} in 
  rewrite dualInv {a=b} in 
  Refl
dualInv {a=Zero}     = Refl
dualInv {a=Top}      = Refl
dualInv {a=ExpL a}   = rewrite dualInv {a} in Refl
dualInv {a=ExpR a}   = rewrite dualInv {a} in Refl

mutual 
  data Cmd : List Ty -> List Ty -> Type where 
    C  : Term k g a -> Term k d (dual a) -> Cmd k (g ++ d)
    PC : Cmd k (g ++ a::b::d) -> Cmd k (g ++ b::a::d) 
    -- we probably also need to permute duplicable contexts

  data Term : List Ty -> List Ty -> Ty -> Type where
    Var    : Term k [a] a
    VarD   : Term (a::k) [] a
    Covar  : Term k [a] (dual a)
    CovarD : Term (a::k) [] (dual a)
    Tup    : Term k g t -> Term k d u -> Term k (g++d) (Ten t u)
    Mat    : Cmd k (a::b::g) -> Term k g (Par (dual a) (dual b))
    Triv   : Term k [] One
    ESt    : Cmd k g -> Term k g Bot  
    Inl    : Term k g t -> Term k g (Sum t u)
    Inr    : Term k g u -> Term k g (Sum t u)
    Rec    : Cmd k (a::g) -> Cmd k (b::g) -> Term k g (With (dual a) (dual b))
    EMat   : Term k g Top
    Mu     : Cmd k (a::g) -> Term k g (dual a)
    Dup    : Term k [] a -> Term k [] (ExpL a)
    Codup  : Cmd (a::k) g -> Term k g (ExpR (dual a))

forwardCmd : (g, s, d : List Ty) -> (a : Ty) -> Cmd k ((g++s)++(a::d)) -> Cmd k ((g++a::s)++d)
forwardCmd g []      d a c = 
  rewrite sym $ appendAssociative g [a] d in 
  rewrite sym $ appendNilRightNeutral g in 
  c
forwardCmd g (s::ss) d a c = 
  rewrite sym $ appendAssociative g (a::s::ss) d in 
  PC {a=s} {b=a} {g} {d=ss++d} $ 
  rewrite appendAssociative g [s] (a::ss ++ d) in 
  rewrite appendAssociative (g++[s]) (a::ss) d in 
  forwardCmd (g++[s]) ss d a $ 
  rewrite sym $ appendAssociative g [s] ss in
  c

permuteCmd : (g, s, p, d : List Ty) -> Cmd k ((g++s)++(p++d)) -> Cmd k ((g++p)++(s++d))
permuteCmd g s [] d c = 
  rewrite appendNilRightNeutral g in 
  rewrite appendAssociative g s d in 
  c
permuteCmd g s (p::ps) d c = 
  rewrite appendAssociative g [p] ps in 
  permuteCmd (g++[p]) s ps d $
  rewrite sym $ appendAssociative g [p] s in
  forwardCmd g s (ps++d) p c

permuteCmd' : (g, s, p : List Ty) -> Cmd k ((g++s)++p) -> Cmd k ((g++p)++s)
permuteCmd' g s p = 
  rewrite sym $ appendNilRightNeutral ((g ++ s) ++ p) in
  rewrite sym $ appendNilRightNeutral ((g ++ p) ++ s) in
  rewrite sym $ appendAssociative (g ++ s) p [] in
  rewrite sym $ appendAssociative (g ++ p) s [] in
  permuteCmd g s p []

dupD : Term [a] [] (Ten (ExpL a) (ExpL a))
dupD = Tup {g=[]} {d=[]} (Dup VarD) (Dup VarD)

dupL : Term [] [ExpL a] (Ten (ExpL a) (ExpL a))
dupL {a} = 
  rewrite sym $ dualInv {a} in 
  Mu {a=Par (ExpR (dual a)) (ExpR (dual a))} $ 
  permuteCmd' [] [ExpL (dual (dual a))] [Par (ExpR (dual a)) (ExpR (dual a))]  $  
  C {a=ExpL (dual (dual a))} {g=[ExpL (dual (dual a))]} {d=[Par (ExpR (dual a)) (ExpR (dual a))]} 
    Var 
    (rewrite dualInv {a} in 
     Codup {a} $ 
     C {a=Par (ExpR (dual a)) (ExpR (dual a))} {g=[Par (ExpR (dual a)) (ExpR (dual a))]} {d=[]} 
       Var
       (rewrite dualInv {a} in  
        Tup {k=[a]} {g=[]} {d=[]} (Dup VarD) (Dup VarD)
       )
    )
