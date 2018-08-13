module Levy.Syntax

%access public export
%default total

-- The type of variable names.
Name : Type
Name = String

-- Levy types are separated into value types and computation types, but
-- it is convenient to have a single datatype for all of them.
mutual
  data LTypeS = VIntS                 -- integer [int]
              | VBoolS                -- booleans [bool]
              | VForgetS CTypeS       -- thunked type [U t]
              | CFreeS VTypeS         -- free type [F s]    
              | CArrowS VTypeS CTypeS -- Function type [s -> t]

  CTypeS : Type
  CTypeS = LTypeS
   
  VTypeS : Type
  VTypeS = LTypeS

-- Levy expressions. We actually use the same type for values
-- and computations because it makes the code shorter and produces
-- more reasonable error messages during type checking.
mutual   
  Val : Type
  Val = Expr

  data Expr = Var    Name             -- variable
            | EInt   Integer          -- integer constant
            | EBool  Bool             -- boolean constant
            | Times  Val  Val         -- product [v1 * v2]
            | Plus   Val  Val         -- sum [v1 + v2]
            | Minus  Val  Val         -- difference [v1 - v2]
            | Equal  Val  Val         -- integer equality [v1 = v2]
            | Less   Val  Val         -- integer comparison [v1 < v2]
            | Thunk  Expr             -- thunk [thunk e]
            | Force  Val              -- [force v]
            | Return Val              -- [return v]
            | Do     Name Expr   Expr -- sequencing [do x <- e1 in e2]
            | Let    Name Val    Expr -- let-binding [let x = v in e]
            | If     Val  Expr   Expr -- conditional [if v then e1 else e2]
            | Fun    Name LTypeS Expr -- function [fun x:s -> e]
            | Apply  Expr Val         -- application [e v]
            | Rec    Name LTypeS Expr -- recursion [rec x : t is e]

data TopLevelCmd = TLExpr Expr
                 | TLDef Name Expr
             --   | RunDef Name Expr
             --   | Use String
             --   | Quit
