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

mayStr : (TOK -> Maybe String) -> All (Parser' String)   
mayStr = maybeTok

isVAR : TOK -> Maybe String
isVAR (VAR v) = Just v
isVAR _       = Nothing

expr : All (Parser' Expr)
expr = alts [ cmap (EBool True)  $ ex TRUE
            , cmap (EBool False) $ ex FALSE
            ]

toplevel : All (Parser' TopLevelCmd)
toplevel = alts [ map (\(n,e) => TLDef n e) $ 
                  rand (ex LET) (and (mayStr isVAR) (rand (ex EQUAL) expr))
                , map TLExpr expr 
                ]
