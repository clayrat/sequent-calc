
module ABS.AI

import ABS.L

%default total
%access public export

-- lambda-db and its compilation to an abstract instruction set

data DB = DBvar Nat 
        | DBlam DB 
        | DBapp DB DB 

data I = Exec
       | Clear I
       | Closure I I
       | Pusharg I
       | Poparg I
       | Extendenv I
       | Lookupenv I

compile : DB -> I
compile (DBvar Z)     = Lookupenv $ Exec
compile (DBvar (S n)) = Lookupenv $ Clear $ assert_total $ compile (DBvar n)
compile (DBlam t)     = Poparg $ Extendenv $ compile t
compile (DBapp t1 t2) = Closure (compile t2) $ Pusharg $ compile t1

-- compilation of abstract instruction set into lambda-mu-mu-r-^

embedI : I -> C
embedI  Exec          = Bar (Vweak (Vweak Acc Wstack) Wenv) (Eweak (Eweak Stack Wacc) Wenv)
embedI (Clear c)      = Cweak (embedI c) Wacc
embedI (Closure c c') = Bar (Vweak (Mustack $ embedI c) Wstack) (Mub $ embedI c')
embedI (Pusharg c)    = Bar (Vweak (Vweak (Mustack $ embedI c) Wstack) Wacc) (Cons (Vweak (Vweak Acc Wstack) Wenv) (Eweak (Eweak Stack Wacc) Wenv))
embedI (Poparg c)     = Bar (Vweak (Lam (Mustack $ embedI c)) Wstack) (Eweak Stack Wenv) 
embedI (Extendenv c)  = Bar (Vweak (Vweak (Muenv $ embedI c) Wacc) Wenv) (Cons (Vweak (Vweak Acc Wstack) Wenv) (Eweak (Eweak Env Wstack) Wacc)) 
embedI (Lookupenv c)  = Bar (Vweak (Lam (Muenv $ embedI c)) Wenv) (Eweak Env Wstack)
