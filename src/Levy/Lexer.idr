module Levy.Lexer

import TParsec.Running

%access public export
%default total

mutual
  data TOK : Type where
    VINT     : Int -> TOK
    TFORGET  : TOK
    TFREE    : TOK
    TARROW   : TOK
    TBOOL    : TOK
    TINT     : TOK
    DO       : TOK
    ELSE     : TOK
    FALSE    : TOK
    FORCE    : TOK
    FUN      : TOK
    IF       : TOK
    IN       : TOK
    IS       : TOK
    LET      : TOK
    REC      : TOK
    RETURN   : TOK
    THEN     : TOK
    THUNK    : TOK
    TRUE     : TOK
    SEMISEMI : TOK
    LPAREN   : TOK
    RPAREN   : TOK
    TIMES    : TOK
    PLUS     : TOK
    MINUS    : TOK
    COLON    : TOK
    LESS     : TOK
    EQUAL    : TOK
    DARROW   : TOK
    ASSIGN   : TOK
    VAR      : String -> TOK
    IGNORE   : TOK   --hacky

Eq TOK where
  (==) (VINT a)  (VINT b)  = a == b
  (==)  TFORGET   TFORGET  = True
  (==)  TFREE     TFREE    = True
  (==)  TARROW    TARROW   = True
  (==)  TBOOL     TBOOL    = True
  (==)  TINT      TINT     = True
  (==)  DO        DO       = True
  (==)  ELSE      ELSE     = True
  (==)  FALSE     FALSE    = True
  (==)  FORCE     FORCE    = True
  (==)  FUN       FUN      = True
  (==)  IF        IF       = True
  (==)  IN        IN       = True
  (==)  IS        IS       = True
  (==)  LET       LET      = True
  (==)  REC       REC      = True
  (==)  RETURN    RETURN   = True
  (==)  THEN      THEN     = True
  (==)  THUNK     THUNK    = True
  (==)  TRUE      TRUE     = True
  (==)  SEMISEMI  SEMISEMI = True
  (==)  LPAREN    LPAREN   = True
  (==)  RPAREN    RPAREN   = True
  (==)  TIMES     TIMES    = True
  (==)  PLUS      PLUS     = True
  (==)  MINUS     MINUS    = True
  (==)  COLON     COLON    = True
  (==)  LESS      LESS     = True
  (==)  EQUAL     EQUAL    = True
  (==)  DARROW    DARROW   = True
  (==)  ASSIGN    ASSIGN   = True
  (==)  IGNORE    IGNORE   = True
  (==) (VAR a)   (VAR b)   = a == b
  (==)  _         _        = False

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
    auxTOK "rec"    = REC     
    auxTOK "return" = RETURN  
    auxTOK "then"   = THEN    
    auxTOK "thunk"  = THUNK   
    auxTOK "true"   = TRUE    
    auxTOK ";;"     = SEMISEMI
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
        let s = strCons x xs in
        if x == '-' && (all isDigit $ unpack s) 
          then VINT (cast {to=Int} s)
          else if (all isDigit $ unpack s) 
            then VINT (cast {to=Int} s) 
            else auxTOK s
