module Levy.Syntax

%access public export
%default total

-- The type of variable names.
Name : Type
Name = String

-- Levy types are separated into value types and computation types
mutual
  data CType = CFree VType        -- free type [F s]    
             | CArrow VType CType -- function type [s -> t]
   
  data VType = VInt               -- integer [int]
             | VBool              -- booleans [bool]
             | VForget CType      -- thunked type [U t]

-- Levy expressions are also values and computations
mutual   
  data Val = Var    Name            -- variable
           | EInt   Integer         -- integer constant
           | EBool  Bool            -- boolean constant
           | Times  Val  Val        -- product [v1 * v2]
           | Plus   Val  Val        -- sum [v1 + v2]
           | Minus  Val  Val        -- difference [v1 - v2]
           | Equal  Val  Val        -- integer equality [v1 = v2]
           | Less   Val  Val        -- integer comparison [v1 < v2]
           | Thunk  Expr            -- thunk [thunk e]

  data Expr = Force  Val             -- [force v]
            | Return Val             -- [return v]
            | Do     Name Expr  Expr -- sequencing [do x <- e1 in e2]
            | Let    Name Val   Expr -- let-binding [let x = v in e]
            | If     Val  Expr  Expr -- conditional [if v then e1 else e2]
            | Fun    Name VType Expr -- function [fun x:s -> e]
            | Apply  Expr Val        -- application [e v]
            | Rec    Name CType Expr -- recursion [rec x : t is e]

data TopLevelCmd = TLExpr Expr
                 | TLDef Name Val
             --   | RunDef Name Expr
             --   | Use String
             --   | Quit
