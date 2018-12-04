module ABS.L

-- port of http://www.cs.indiana.edu/~sabry/papers/sequent_code.tar

%default total
%access public export

-- Syntax

-- weakenings
data W = Wacc | Wstack | Wenv 

mutual 
  -- commands
  data C = Bar V E 
         | Csub C T 
         | Cweak C W 
  
  -- terms
  data V = Acc 
         | Lam V 
         | Mustack C 
         | Muenv C 
         | Vsub V T 
         | Vweak V W 

  -- contexts        
  data E = Tp 
         | Stack 
         | Env
         | Cons V E 
         | Mub C 
         | Esub E T 
         | Eweak E W 
  
  -- substitutions
  data T = Sacc V 
         | Sstack E
         | Senv E 
  
-- Pretty-printing

Show W where
    show Wacc = "^r"
    show Wstack = "^s"
    show Wenv = "^e"

mutual
  Show C where
    show (Bar v e) = "<" ++ show v ++ " | " ++ show e ++ ">"
    show (Csub c t) = show c ++ show t
    show (Cweak c w) = show c ++ show w
  
  Show V where
    show Acc = "r" 
    show (Lam v) = "(\\r. " ++ show v ++ ")"
    show (Mustack c) = "(mu s. " ++ show c ++ ")"
    show (Muenv c) = "(mu e. " ++ show c ++ ")"
    show (Vsub v t) = show v ++ show t
    show (Vweak v w) = show v ++ show w
  
  Show E where
    show Tp = "tp" 
    show Stack = "s" 
    show Env = "e" 
    show (Cons v e) = "(" ++ show v ++ " . " ++ show e ++ ")"
    show (Mub c) = "(mub r. " ++ show c ++ ")"
    show (Esub e t) = show e ++ show t
    show (Eweak e w) = show e ++ show w
  
  Show T where
    show (Sacc v) = "[r <- " ++ show v ++ "]"
    show (Sstack e) = "[s <- " ++ show e ++ "]"
    show (Senv e) = "[e <- " ++ show e ++ "]"

