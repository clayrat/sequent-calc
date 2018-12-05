module ABS.Value.L

import ABS.L

%default total
%access public export

step : C -> Maybe C                                             
step (Bar v e) =                                               
    -- Try to simplify the term and the context                  
    ((\w => Bar w e) <$> redv v)
    <|>
    ((Bar v) <$> rede e)
    -- Look at term                                              
    <|>
    (case v of                                                   
      Mustack c' => Just $ Csub c' (Sstack e)                  
      Muenv c'   => Just $ Csub c' (Senv e)                      
      v => case (v,e) of                                         
             (Lam bv, Cons v' e') => Just $ Bar v' (Mub (Bar bv (Eweak e' Wacc)))
             (v     , Mub c'    ) => Just $ Csub c' (Sacc v)             
             _ => Nothing)                                       
step c = redc c
