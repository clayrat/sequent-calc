module Levy.Lexer

import TParsec.Running

%access public export
%default total

mutual
  data TOK : Type where
    VINT    : Integer -> TOK
    TFORGET : TOK
    TFREE   : TOK
    TARROW  : TOK
    TBOOL   : TOK
    TINT    : TOK
    DO      : TOK
    ELSE    : TOK
    FALSE   : TOK
    FORCE   : TOK
    FUN     : TOK
    IF      : TOK
    IN      : TOK
    IS      : TOK
    LET     : TOK
    TOPLET  : TOK  -- hacky
    REC     : TOK
    RETURN  : TOK
    THEN    : TOK
    THUNK   : TOK
    TRUE    : TOK
    SEMI    : TOK
    APP     : TOK  -- hacky
    LPAREN  : TOK
    RPAREN  : TOK
    TIMES   : TOK
    PLUS    : TOK
    MINUS   : TOK
    COLON   : TOK
    LESS    : TOK
    EQUAL   : TOK
    DARROW  : TOK
    ASSIGN  : TOK
    VAR     : String -> TOK
    IGNORE  : TOK   --hacky

Eq TOK where
  (==) (VINT a) (VINT b) = a == b
  (==)  TFORGET  TFORGET = True
  (==)  TFREE    TFREE   = True
  (==)  TARROW   TARROW  = True
  (==)  TBOOL    TBOOL   = True
  (==)  TINT     TINT    = True
  (==)  DO       DO      = True
  (==)  ELSE     ELSE    = True
  (==)  FALSE    FALSE   = True
  (==)  FORCE    FORCE   = True
  (==)  FUN      FUN     = True
  (==)  IF       IF      = True
  (==)  IN       IN      = True
  (==)  IS       IS      = True
  (==)  LET      LET     = True
  (==)  TOPLET   TOPLET  = True
  (==)  REC      REC     = True
  (==)  RETURN   RETURN  = True
  (==)  THEN     THEN    = True
  (==)  THUNK    THUNK   = True
  (==)  TRUE     TRUE    = True
  (==)  SEMI     SEMI    = True
  (==)  APP      APP     = True
  (==)  LPAREN   LPAREN  = True
  (==)  RPAREN   RPAREN  = True
  (==)  TIMES    TIMES   = True
  (==)  PLUS     PLUS    = True
  (==)  MINUS    MINUS   = True
  (==)  COLON    COLON   = True
  (==)  LESS     LESS    = True
  (==)  EQUAL    EQUAL   = True
  (==)  DARROW   DARROW  = True
  (==)  ASSIGN   ASSIGN  = True
  (==)  IGNORE   IGNORE  = True
  (==) (VAR a)  (VAR b)  = a == b
  (==)  _        _       = False

Tokenizer TOK where         
  tokenize = map toTOK . words
    where
    auxTOK : String -> TOK
    auxTOK "U"      = TFORGET 
    auxTOK "F"      = TFREE   
    auxTOK "->"     = TARROW  
    auxTOK "bool"   = TBOOL   
    auxTOK "int"    = TINT    
    auxTOK "do"     = DO      
    auxTOK "else"   = ELSE    
    auxTOK "false"  = FALSE   
    auxTOK "force"  = FORCE   
    auxTOK "fun"    = FUN     
    auxTOK "if"     = IF      
    auxTOK "in"     = IN      
    auxTOK "is"     = IS      
    auxTOK "let"    = LET     
    auxTOK "let_"   = TOPLET  
    auxTOK "rec"    = REC     
    auxTOK "return" = RETURN  
    auxTOK "then"   = THEN    
    auxTOK "thunk"  = THUNK   
    auxTOK "true"   = TRUE    
    auxTOK ";"      = SEMI
    auxTOK "$"      = APP
    auxTOK "("      = LPAREN  
    auxTOK ")"      = RPAREN  
    auxTOK "*"      = TIMES   
    auxTOK "+"      = PLUS    
    auxTOK "-"      = MINUS   
    auxTOK ":"      = COLON   
    auxTOK "<"      = LESS    
    auxTOK "="      = EQUAL   
    auxTOK "=>"     = DARROW  
    auxTOK "<-"     = ASSIGN  
    auxTOK v        = VAR v
    toTOK : String -> TOK
    toTOK s with (strM s)
      toTOK "" | StrNil = IGNORE
      toTOK (strCons x xs) | StrCons x xs = 
        let s = strCons x xs 
            xsc = unpack xs
          in  
        if x == '-' && length xsc > 0 && all isDigit xsc
          then VINT (cast {to=Integer} s)
          else 
            let sc = unpack s in
              if length sc > 0 && all isDigit sc
              then VINT (cast {to=Integer} s) 
              else auxTOK s
