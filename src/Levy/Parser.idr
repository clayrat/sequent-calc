module Levy.Parser

import Control.Monad.State
import Data.NEList
import TParsec
import TParsec.Running
import Levy.Lexer
import Levy.Syntax

%access public export
%default total

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok TOK)

-- workarounds for #4504   
ex : TOK -> All (Parser' TOK)   
ex = exact

fromVar : All (Parser' String)   
fromVar = maybeTok isVAR
  where
  isVAR : TOK -> Maybe String
  isVAR (VAR v) = Just v
  isVAR _       = Nothing

fromVInt : All (Parser' Integer)   
fromVInt = maybeTok isVINT
  where
  isVINT : TOK -> Maybe Integer
  isVINT (VINT i) = Just i
  isVINT _        = Nothing

andx : All (Box (Parser' s) :-> Box (Parser' t) :-> Box (Parser' (s, t)))      
andx p q =                                                               
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q  

expr : All (Parser' Expr)
expr = fix _ $ \rec =>
  let 
    simple = alts [ map Var                   $ fromVar
                  , map EInt                  $ fromVInt
                  , cmap (EBool True)         $ ex TRUE
                  , cmap (EBool False)        $ ex FALSE
                  ]
  in
  alts [ simple
       , map (\(n,v,e) => Let n v e) $ 
         rand (ex LET) $ and fromVar $ rand (ex EQUAL) $ andx rec $ rand (ex IN) rec
       , map (\(n,e1,e2) => Do n e1 e2) $ 
         rand (ex DO) $ and fromVar $ rand (ex ASSIGN) $ andx rec $ rand (ex IN) rec
       , map (\(i,t,e) => If i t e) $ 
         rand (ex IF) $ andx rec $ rand (ex THEN) $ andx rec $ rand (ex ELSE) rec
       ]

toplevel : All (Parser' TopLevelCmd)
toplevel = alts [ --map (\(n,e) => TLDef n e) $ 
                  --rand (ex LET) $ and fromVar $ rand (ex EQUAL) expr
                --, 
                  map TLExpr expr 
                ]
