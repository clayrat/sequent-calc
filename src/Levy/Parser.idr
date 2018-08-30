module Levy.Parser

import Control.Monad.State
import Data.DList
import Data.NEList
import TParsec
import Levy.Lexer
import Levy.Syntax

%access public export
%default total

Parser' : Type -> Nat -> Type
Parser' = Parser TParsecU (sizedtok TOK)

andx : All (Box (Parser' s) :-> Box (Parser' t) :-> Box (Parser' (s, t)))      
andx p q =                                                               
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.and p q) p q  

altx : All (Box (Parser' a) :-> Box (Parser' a) :-> Box (Parser' a))
altx p q =                                                               
  Nat.map2 {a=Parser' _} {b=Parser' _} (\p, q => Combinators.alt p q) p q  

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

-- Types  

vty : All (Box (Parser' CType) :-> Parser' VType) 
vty pc = alts [ cmap VInt    $ ex TINT
              , cmap VBool   $ ex TBOOL
              , map  VForget $ rand (ex TFORGET) $ altx (between (ex LPAREN) (ex RPAREN) pc) pc
              ]

cty : All (Box (Parser' CType) :-> Parser' CType)
cty rec = alts [ map CFree $ rand (ex TFREE) $ altx (between (ex LPAREN) (ex RPAREN) (vty rec)) (vty rec)
               , map (\(v,c) => CArrow v c) $ and (vty rec) $ rand (ex TARROW) rec
               ]

record Ty (n : Nat) where
  constructor MkTy
  pvty : Parser' VType n      
  pcty : Parser' CType n    
  
ty : All Ty
ty = fix _ $ \rec =>
  let ihс = Nat.map {a=Ty} pcty rec in 
  MkTy (vty ihс) (cty ihс)

-- Terms  

val : All (Box (Parser' Expr) :-> Box (Parser' Val) :-> Parser' Val)  
val pe rec = 
  let 
    v = alts [ map Thunk          $ rand (ex THUNK) pe
             , map Var            $ fromVar
             , map EInt           $ fromVInt
             , cmap (EBool True)  $ ex TRUE
             , cmap (EBool False) $ ex FALSE
             , between (ex LPAREN) (ex RPAREN) rec
             ]
    factor = chainl1 v (cmap Times $ ex TIMES)
    arop = (cmap Plus $ ex PLUS) `alt` (cmap Minus $ ex MINUS) 
    arith = chainl1 factor arop 
    in
    alts [ map (\(x,y) => Equal x y) $ and arith $ rand (ex EQUAL) arith
         , map (\(x,y) => Less x y)  $ and arith $ rand (ex LESS)  arith
         , arith 
         ]

expr : All (Box (Parser' Expr) :-> Box (Parser' Val) :-> Parser' Expr)
expr rec pv =
  let 
    free = alt (map Force $ rand (ex FORCE) (val rec pv)) 
               (map Return $ rand (ex RETURN) (val rec pv)) 
    freeb = alt (between (ex LPAREN) (ex RPAREN) free) free
    e = alts [ hchainl freeb (cmap Apply $ ex APP) (val rec pv)
             , map (\(n,v,e) => Let n v e) $ 
               rand (ex LET) $ and fromVar $ rand (ex EQUAL) $ and (val rec pv) $ rand (ex IN) rec
             , map (\(n,e1,e2) => Do n e1 e2) $ 
               rand (ex DO) $ and fromVar $ rand (ex ASSIGN) $ andx rec $ rand (ex IN) rec
             , map (\(i,t,e) => If i t e) $ 
               rand (ex IF) $ and (val rec pv) $ rand (ex THEN) $ andx rec $ rand (ex ELSE) rec
             , map (\(n,t,e) => Fun n t e) $ 
               rand (ex FUN) $ and fromVar $ rand (ex COLON) $ andx (pvty ty) $ rand (ex DARROW) rec
             , map (\(n,t,e) => Rec n t e) $ 
               rand (ex REC) $ and fromVar $ rand (ex COLON) $ andx (pcty ty) $ rand (ex IS) rec
             ]
    in
   alt (between (ex LPAREN) (ex RPAREN) e) e

record Term (n : Nat) where
  constructor MkTerm
  pval : Parser' Val n      
  pexp : Parser' Expr n    
  
term : All Term
term = fix _ $ \rec =>
  let 
    ihe = Nat.map {a=Term} pexp rec 
    ihv = Nat.map {a=Term} pval rec 
    in 
  MkTerm (val ihe ihv) (expr ihe ihv)

-- Toplevel commands  

toplevel : All (Parser' TopLevelCmd)
toplevel = alts [ map (\(n,e) => TLDef n e) $ 
                  rand (ex TOPLET) $ and fromVar $ rand (ex EQUAL) (pval term)
                , map TLExpr (pexp term)
                ]

file : All (Parser' (List TopLevelCmd))
file = map DList.toList $ chainl1 (map wrap toplevel) (cmap (++) $ ex SEMI)
