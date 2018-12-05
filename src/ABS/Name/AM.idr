module ABS.Name.AM

import ABS.L
import ABS.AI

%default total
%access public export

-- Abstract machine

mutual
  Env : Type 
  Env = List Clos

  data Clos = MkClos (I, Env)

Stack : Type
Stack = List Clos

Acc : Type
Acc = Clos

State : Type
State = (I, Env, Stack, Maybe Acc)

step : State -> Maybe State
step (Exec        ,    _,    s, Just (MkClos (c, e'))) = Just (c ,    e',    s, Nothing             )
step (Clear c     ,    e,    s, _                    ) = Just (c ,    e ,    s, Nothing             )
step (Closure c c',    e,    s, Nothing              ) = Just (c',    e ,    s, Just (MkClos (c, e)))
step (Pusharg c   ,    e,    s, Just v               ) = Just (c ,    e , v::s, Nothing             )
step (Poparg c    ,    e, v::s, Nothing              ) = Just (c ,    e ,    s, Just v              )
step (Extendenv c ,    e,    s, Just v               ) = Just (c , v::e ,    s, Nothing             )
step (Lookupenv c , v::e,    s, Nothing              ) = Just (c ,    e ,    s, Just v              )
step _ = Nothing

-- Embedding abstract machine states into lambda-mu-mu-r-^

mutual
  embedacc : Acc -> V
  embedacc (MkClos (c, e)) = Mustack (Csub (embedI c) (Senv (Eweak (embedenv e) Wstack)))

  embedenv : Env -> E
  embedenv = foldr (Cons . embedacc) Tp

embedstack : Stack -> E
embedstack = foldr (Cons . embedacc) Tp

embedstate : State -> C
embedstate (c, e, s, Nothing)  =       Csub (Csub (embedI c) (Senv        (Eweak (embedenv e) Wstack)      )) (Sstack $       embedstack s)
embedstate (c, e, s, Just acc) = Csub (Csub (Csub (embedI c) (Senv (Eweak (Eweak (embedenv e) Wstack) Wacc))) (Sstack (Eweak (embedstack s) Wacc))) (Sacc $ embedacc acc)

eval : I -> (Nat, C)
eval is = loop Z (is, [], [], Nothing)
  where 
  loop : Nat -> State -> (Nat, C)  
  loop i s = case step s of
    Nothing => (i, embedstate s)
    Just s' => assert_total $ loop (S i) s'
