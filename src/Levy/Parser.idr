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

andx : All (Box (Parser' s) :-> Box (Parser' t) :-> Box (Parser' (s, t)))      
andx p q =                                                               
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q  

-- workarounds for #4504   
ex : TOK -> All (Parser' TOK)   
ex = exact

fromVar : All (Parser' String)   
fromVar = maybeTok $ \t => case t of 
  VAR v => Just v
  _     => Nothing

fromVInt : All (Parser' Integer)   
fromVInt = maybeTok $ \t => case t of 
  VINT i => Just i
  _      => Nothing

ty : All (Parser' LTypeS)
ty = fix _ $ \rec =>
       let 
         arr = cmap CArrowS $ ex TARROW 
         t = alts [ cmap VIntS   $ ex TINT
                  , cmap VBoolS  $ ex TBOOL
                  , between (ex LPAREN) (ex RPAREN) rec 
                  ]
         app = alts [ t 
                    , map VForgetS $ rand (ex TFORGET) t
                    , map CFreeS   $ rand (ex TFREE) t
                    ]
         in 
       chainr1 app arr

expr : All (Parser' Expr)
expr = fix _ $ \rec =>
  let 
    e = alts [ map Var            $ fromVar
             , map EInt           $ fromVInt
             , cmap (EBool True)  $ ex TRUE
             , cmap (EBool False) $ ex FALSE
             , between (ex LPAREN) (ex RPAREN) rec
             ]
    rapp = alts [ map Force  $ rand (ex FORCE)  e
                , map Return $ rand (ex RETURN) e
                , map Thunk  $ rand (ex THUNK)  e
                , e
                ]
    app = chainl1 rapp (cmap Apply $ ex APP)               
    factor = chainl1 app (cmap Times $ ex TIMES)
    arop = (cmap Plus $ ex PLUS) `alt` (cmap Minus $ ex MINUS) 
    arith = chainl1 factor arop 
    bool = alts [ map (\(x,y) => Equal x y) $ and arith $ rand (ex EQUAL) arith
                , map (\(x,y) => Less x y)  $ and arith $ rand (ex LESS)  arith
                , arith 
                ]
    in
  alts [ bool
       , map (\(n,v,e) => Let n v e) $ 
         rand (ex LET) $ and fromVar $ rand (ex EQUAL) $ andx rec $ rand (ex IN) rec
       , map (\(n,e1,e2) => Do n e1 e2) $ 
         rand (ex DO) $ and fromVar $ rand (ex ASSIGN) $ andx rec $ rand (ex IN) rec
       , map (\(i,t,e) => If i t e) $ 
         rand (ex IF) $ andx rec $ rand (ex THEN) $ andx rec $ rand (ex ELSE) rec
       , map (\(n,t,e) => Fun n t e) $ 
         rand (ex FUN) $ and fromVar $ rand (ex COLON) $ andx ty $ rand (ex DARROW) rec
       , map (\(n,t,e) => Rec n t e) $ 
         rand (ex REC) $ and fromVar $ rand (ex COLON) $ andx ty $ rand (ex IS) rec
       ]
  
toplevel : All (Parser' TopLevelCmd)
toplevel = alts [ map (\(n,e) => TLDef n e) $ 
                  rand (ex TOPLET) $ and fromVar $ rand (ex EQUAL) expr
                , map TLExpr expr 
                ]