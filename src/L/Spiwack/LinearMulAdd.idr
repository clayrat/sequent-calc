module L.LinearMulAdd

%access public export
%default total

data Ty = AL | AR 
        | Ten Ty Ty | Par  Ty Ty | One  | Bot
        | Sum Ty Ty | With Ty Ty | Zero | Top  

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

mutual 
  data Cmd : List Ty -> Type where 
    C  : Term g a -> Term d (dual a) -> Cmd (g ++ d)
    PC : Cmd (g ++ a::b::d) -> Cmd (g ++ b::a::d) 

  data Term : List Ty -> Ty -> Type where
    Var   : Term [a] a
    Covar : Term [a] (dual a)
    Tup   : Term g t -> Term d u -> Term (g++d) (Ten t u)
    Mat   : Cmd (a::b::g) -> Term g (Par (dual a) (dual b))
    Triv  : Term [] One
    ESt   : Cmd g -> Term g Bot  
    Inl   : Term g t -> Term g (Sum t u)
    Inr   : Term g u -> Term g (Sum t u)
    Rec   : Cmd (a::g) -> Cmd (b::g) -> Term g (With (dual a) (dual b))
    EMat  : Term g Top
    Mu    : Cmd (a::g) -> Term g (dual a)

forwardCmd : (g, s, d : List Ty) -> (a : Ty) -> Cmd ((g++s)++(a::d)) -> Cmd ((g++a::s)++d)
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

permuteCmd : (g, s, p, d : List Ty) -> Cmd ((g++s)++(p++d)) -> Cmd ((g++p)++(s++d))
permuteCmd g s [] d c = 
  rewrite appendNilRightNeutral g in 
  rewrite appendAssociative g s d in 
  c
permuteCmd g s (p::ps) d c = 
  rewrite appendAssociative g [p] ps in 
  permuteCmd (g++[p]) s ps d $
  rewrite sym $ appendAssociative g [p] s in
  forwardCmd g s (ps++d) p c

permuteCmd' : (g, s, p : List Ty) -> Cmd ((g++s)++p) -> Cmd ((g++p)++s)
permuteCmd' g s p = 
  rewrite sym $ appendNilRightNeutral ((g ++ s) ++ p) in
  rewrite sym $ appendNilRightNeutral ((g ++ p) ++ s) in
  rewrite sym $ appendAssociative (g ++ s) p [] in
  rewrite sym $ appendAssociative (g ++ p) s [] in
  permuteCmd g s p []
  
Imp : Ty -> Ty -> Ty
Imp a b = Par (dual a) (dual b)

lam : Term (a::g) b -> Term g (Imp a b)
lam t {a} {b} {g} = 
  Mat $ permuteCmd' [a] g [b] $ C t (Covar {a=b})

app : Term g (Imp a b) -> Term d a -> Term (g++d) b
app {a} {b} {g} {d} t u = 
  rewrite sym $ dualInv {a=b} in 
  Mu {a=dual b} $ 
  permuteCmd [] g [dual b] d $ 
  rewrite appendAssociative g [dual b] d in
  permuteCmd' g d [dual b] $ 
  rewrite sym $ appendAssociative g d [dual b] in
  C t (Tup (rewrite dualInv {a} in u) (Covar {a=dual b}))

recTerm : Term g a -> Term g b -> Term g (With a b)
recTerm {a} {b} {g} t u = 
  rewrite sym $ dualInv {a} in 
  rewrite sym $ dualInv {a=b} in 
  Rec {a=dual a} {b=dual b} 
    (permuteCmd' [] g [dual a] $ 
     C {d=[dual a]} t Var) 
    (permuteCmd' [] g [dual b] $ 
     C {d=[dual b]} u Var)

proj1 : Term g (With a b) -> Term g a  
proj1 {a} {g} t = 
  rewrite sym $ dualInv {a} in 
  Mu {a=dual a} $ 
  permuteCmd' [] g [dual a] $  
  C {d=[dual a]} t $ 
  Inl Var

proj2 : Term g (With a b) -> Term g b
proj2 {b} {g} t = 
  rewrite sym $ dualInv {a=b} in 
  Mu {a=dual b} $ 
  permuteCmd' [] g [dual b] $  
  C {d=[dual b]} t $ 
  Inr Var  


--reduce : Cmd g -> (d ** Cmd d)
--reduce (C (Mu c1)  t     ) = ?wat
--reduce (C t       (Mu c2)) = ?wat2
--reduce (C Triv    (ESt {g} c)) = (g ** c)

