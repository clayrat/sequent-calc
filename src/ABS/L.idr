module ABS.L

%default total
%access public export

-- Syntax and reductions of the l-mu-mubar-r-^ calculus

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

-- Free vars

binding : T -> String
binding (Sacc _)   = "r"
binding (Sstack _) = "a"
binding (Senv _)   = "g"

interface Free m where
  free : m -> List String

Free W where
  free Wacc   = ["r"]
  free Wstack = ["a"]
  free Wenv   = ["g"]

mutual  
  Free C where
    free (Bar v e)   = free v `union` free e 
    free (Csub c t)  = free t `union` delete (binding t) (free c)
    free (Cweak c w) = free c `union` free w
  
  Free V where
    free  Acc        = ["r"]
    free (Lam v)     = delete "r" (free v)
    free (Mustack c) = delete "a" (free c) 
    free (Muenv c)   = delete "g" (free c)
    free (Vsub v t)  = free t `union` delete (binding t) (free v)
    free (Vweak v w) = free v `union` free w
  
  Free E where
    free  Tp         = []
    free  Stack      = ["a"] 
    free  Env        = ["g"]
    free (Cons v e)  = free v `union` free e 
    free (Mub c)     = delete "r" (free c)
    free (Esub e t)  = free t `union` delete (binding t) (free e)
    free (Eweak e w) = free e `union` free w
  
  Free T where
    free (Sacc v)   = free v 
    free (Sstack e) = free e
    free (Senv e)   = free e

-- Helper for reductions                                      
                                                              
has_ewacc : E -> Bool
has_ewacc (Eweak _ Wacc)           = True                             
has_ewacc (Eweak (Eweak _ Wacc) _) = True                   
has_ewacc _                        = False                                           
                                                              
remove_ewacc : E -> E
remove_ewacc (Eweak e Wacc)           = e                             
remove_ewacc (Eweak (Eweak e Wacc) w) = Eweak e w         
remove_ewacc e                        = e                                            
                                                              
--                                                            
                                                              
has_ewstack : E -> Bool
has_ewstack (Eweak _ Wstack)           = True                         
has_ewstack (Eweak (Eweak _ Wstack) _) = True               
has_ewstack _                          = False                                         
                                                              
remove_ewstack : E -> E
remove_ewstack (Eweak e Wstack)           = e                         
remove_ewstack (Eweak (Eweak e Wstack) w) = Eweak e w     
remove_ewstack e                          = e                                          
                                                              
--                                                            
                                                              
has_ewenv : E -> Bool
has_ewenv (Eweak _ Wenv)           = True                             
has_ewenv (Eweak (Eweak _ Wenv) _) = True                   
has_ewenv _                        = False                                           
                                                              
remove_ewenv : E -> E
remove_ewenv (Eweak e Wenv)           = e                             
remove_ewenv (Eweak (Eweak e Wenv) w) = Eweak e w         
remove_ewenv e                        = e                                            
                                                              
--                                                            
                                                              
has_vwstack : V -> Bool
has_vwstack (Vweak _ Wstack)           = True                         
has_vwstack (Vweak (Vweak _ Wstack) _) = True               
has_vwstack _                          = False                                         
                                                              
remove_vwstack : V -> V
remove_vwstack (Vweak v Wstack)           = v            
remove_vwstack (Vweak (Vweak v Wstack) w) = Vweak v w    
remove_vwstack v                          = v            
                                                              
--                                                            
                                                              
has_vwenv : V -> Bool
has_vwenv (Vweak _ Wenv)           = True                     
has_vwenv (Vweak (Vweak _ Wenv) _) = True                     
has_vwenv _                        = False                    
                                                              
remove_vwenv : V -> V
remove_vwenv (Vweak v Wenv)           = v                    
remove_vwenv (Vweak (Vweak v Wenv) w) = Vweak v w          
remove_vwenv v                        = v 

-- Reductions on terms which apply substitutions at the root      
                                                                  
rv : V -> Maybe V                                                
rv (Vsub  Acc             (Sacc   v)) = Just v 

rv (Vsub (Lam v)          (Sstack e)) = Just $ Lam (Vsub v (Sstack (Eweak e Wacc)))              
rv (Vsub (Lam v)          (Senv   e)) = Just $ Lam (Vsub v (Senv   (Eweak e Wacc)))                

rv (Vsub (Mustack c)      (Sacc   v)) = Just $ Mustack (Csub c (Sacc (Vweak v Wstack)))          
rv (Vsub (Muenv   c)      (Sacc   v)) = Just $ Muenv   (Csub c (Sacc (Vweak v Wenv)))              
                                                                  
rv (Vsub (Mustack c)      (Senv   e)) = Just $ Mustack (Csub c (Senv   (Eweak e Wstack)))          
rv (Vsub (Muenv   c)      (Sstack e)) = Just $ Muenv   (Csub c (Sstack (Eweak e Wenv)))            

rv (Vsub (Vweak v Wacc  ) (Sacc   _)) = Just v
rv (Vsub (Vweak v Wstack) (Sstack _)) = Just v
rv (Vsub (Vweak v Wenv  ) (Senv   _)) = Just v
                                                            
rv (Vsub (Vweak v Wacc)   (Sstack e)) = toMaybe (has_ewacc e) $ Vweak (Vsub v (Sstack $ remove_ewacc e)) Wacc 
rv (Vsub (Vweak v Wacc)   (Senv   e)) = toMaybe (has_ewacc e) $ Vweak (Vsub v (Senv   $ remove_ewacc e)) Wacc 
                                                                  
rv (Vsub (Vweak v Wstack) (Senv   e)) = toMaybe (has_ewstack e) $ Vweak (Vsub v (Senv   $ remove_ewstack e)) Wstack
rv (Vsub (Vweak v Wenv)   (Sstack e)) = toMaybe (has_ewenv   e) $ Vweak (Vsub v (Sstack $ remove_ewenv   e)) Wenv 

rv (Vsub (Vweak v Wstack) (Sacc   w)) = toMaybe (has_vwstack w) $ Vweak (Vsub v (Sacc $ remove_vwstack w)) Wstack
rv (Vsub (Vweak v Wenv)   (Sacc   w)) = toMaybe (has_vwenv   w) $ Vweak (Vsub v (Sacc $ remove_vwenv   w)) Wenv       
                                                            
rv _ = Nothing            

-- Allow reductions under two substitutions            
                                                      
rv1 : V -> Maybe V
rv1 (Vsub v t) = (\w => Vsub w t) <$> rv v
rv1 _          = Nothing                                        

rv2 : V -> Maybe V
rv2 (Vsub v t) = (\w => Vsub w t) <$> rv1 v
rv2 _          = Nothing                                        

redv : V -> Maybe V
redv v = (rv v) <|> (rv1 v) <|> (rv2 v)

-- Reductions on contexts which apply substitutions at the root

re : E -> Maybe E 

re (Esub  Stack           (Sstack e)) = Just e
re (Esub  Env             (Senv   e)) = Just e

re (Esub (Cons v e)        t        ) = Just $ Cons (Vsub v t) (Esub e t)

re (Esub (Mub c)          (Sstack e)) = Just $ Mub (Csub c (Sstack (Eweak e Wacc)))
re (Esub (Mub c)          (Senv   e)) = Just $ Mub (Csub c (Senv   (Eweak e Wacc)))

re (Esub (Eweak e Wacc  ) (Sacc   _)) = Just e
re (Esub (Eweak e Wstack) (Sstack _)) = Just e
re (Esub (Eweak e Wenv  ) (Senv   _)) = Just e

re (Esub (Eweak e Wacc)   (Sstack f)) = toMaybe (has_ewacc f) $ Eweak (Esub e (Sstack $ remove_ewacc f)) Wacc
re (Esub (Eweak e Wacc)   (Senv   f)) = toMaybe (has_ewacc f) $ Eweak (Esub e (Senv   $ remove_ewacc f)) Wacc

re (Esub (Eweak e Wstack) (Senv   f)) = toMaybe (has_ewstack f) $ Eweak (Esub e (Senv   $ remove_ewstack f)) Wstack
re (Esub (Eweak e Wenv  ) (Sstack f)) = toMaybe (has_ewenv   f) $ Eweak (Esub e (Sstack $ remove_ewenv   f)) Wenv

re (Esub (Eweak e Wstack) (Sacc   v)) = toMaybe (has_vwstack v) $ Eweak (Esub e (Sacc $ remove_vwstack v)) Wstack
re (Esub (Eweak e Wenv  ) (Sacc   v)) = toMaybe (has_vwenv   v) $ Eweak (Esub e (Sacc $ remove_vwenv   v)) Wenv

re _ = Nothing

-- Allow reductions under two substitutions

re1 : E -> Maybe E 
re1 (Esub e t) = (\f => Esub f t) <$> re e
re1 _          = Nothing

re2 : E -> Maybe E 
re2 (Esub e t) = (\f => Esub f t) <$> re1 e
re2 _          = Nothing

rede : E -> Maybe E 
rede e = (re e) <|> (re1 e) <|> (re2 e)

-- Reductions on commands which apply substitutions at the root 
                                                                
rc : C -> Maybe C                                              
                                                                
rc (Csub (Bar v e)         t        ) = Just $ Bar (Vsub v t) (Esub e t)                      
                                                                
rc (Csub (Cweak c Wacc  ) (Sacc   _)) = Just c                    
rc (Csub (Cweak c Wstack) (Sstack _)) = Just c                
rc (Csub (Cweak c Wenv  ) (Senv   _)) = Just c                    
                                                                
rc (Csub (Cweak c Wacc)   (Sstack e)) = toMaybe (has_ewacc e) $ Cweak (Csub c (Sstack $ remove_ewacc e)) Wacc    
rc (Csub (Cweak c Wacc)   (Senv   e)) = toMaybe (has_ewacc e) $ Cweak (Csub c (Senv   $ remove_ewacc e)) Wacc      
                                                                
rc (Csub (Cweak c Wstack) (Senv   e)) = toMaybe (has_ewstack e) $ Cweak (Csub c (Senv   $ remove_ewstack e)) Wstack  
rc (Csub (Cweak c Wenv  ) (Sstack e)) = toMaybe (has_ewenv   e) $ Cweak (Csub c (Sstack $ remove_ewenv   e)) Wenv    
                                                                
rc (Csub (Cweak c Wstack) (Sacc   v)) = toMaybe (has_vwstack v) $ Cweak (Csub c (Sacc $ remove_vwstack v)) Wstack  
rc (Csub (Cweak c Wenv  ) (Sacc   v)) = toMaybe (has_vwenv   v) $ Cweak (Csub c (Sacc $ remove_vwenv   v)) Wenv      
                                                                
rc _ = Nothing

-- Allow reductions under two substitutions             
                                                        
rc1 : C -> Maybe C                                              
rc1 (Csub c t) = (\d => Csub d t) <$> rc c
rc1 _ = Nothing                                         

rc2 : C -> Maybe C                                              
rc2 (Csub c t) = (\d => Csub d t) <$> rc1 c
rc2 _ = Nothing                                         

redc : C -> Maybe C                                              
redc c = (rc c) <|> (rc1 c) <|> (rc2 c)         

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

-- Evaluation
eval : (C -> Maybe C) -> C -> (Nat, C)
eval step c = loop Z (Csub (Csub c (Senv (Eweak Tp Wstack))) (Sstack Tp))
  where 
  loop : Nat -> C -> (Nat, C)  
  loop i c = case step c of 
    Nothing => (i, c)
    Just c' => assert_total $ loop (S i) c'
