module ABS.Name.L

import ABS.L

%default total
%access public export

step : C -> Maybe C
step (Bar v e) = 
    -- Try to simplify the context and the term
    ((Bar v) <$> rede e)
    <|>
    ((\w => Bar w e) <$> redv v)
    -- Look at context
    <|>
    (case e of 
      Mub c => Just $ Csub c (Sacc v)
     -- Need to make progress with the term
      e => case (v,e) of
             (Lam bv    , Cons v' e') => Just $ Bar v' (Mub (Bar bv (Eweak e' Wacc)))
             (Mustack c', e         ) => Just $ Csub c' (Sstack e)
             (Muenv c'  , e         ) => Just $ Csub c' (Senv e)
             _ => Nothing)
step c = redc c
