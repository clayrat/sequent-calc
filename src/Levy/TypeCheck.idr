module Levy.TypeCheck

import Data.SortedMap
import Text.PrettyPrint.WL
import Levy.Syntax

%access public export
%default total

-- Type checking

mutual 
  Eq CType where
    (CFree v1) == (CFree v2) = v1 == v2
    (CArrow v1 c1) == (CArrow v2 c2) = v1 == v2 && c1 == c2
    _ == _ = False

  Eq VType where
    VInt == VInt = True  
    VBool == VBool = True  
    (VForget c1) == (VForget c2) = c1 == c2
    _ == _ = False

mutual 
  printVType : VType -> Doc
  printVType  VInt         = text "int"
  printVType  VBool        = text "bool"
  printVType (VForget cty) = parens $ text "U" |++| printCType cty

  printCType : CType -> Doc
  printCType (CFree vty)      = parens $ text "F" |++| printVType vty
  printCType (CArrow vty cty) = parens $ printVType vty |+| text " ->" |++| printCType cty

Ctx : Type
Ctx = SortedMap Name VType

-- [check ctx ty e] checks that expression [e] has computation
-- type [ty] in context [ctx].  It raises a type error if it does
-- not.
mutual 
  checkVType : Ctx -> VType -> Val -> Either Doc ()
  checkVType ctx vty v = do vty' <- vtypeOf ctx v
                            if vty' /= vty 
                               then Left $ text "this expression has value type" |++| printVType vty' |++| text "but is used as if its type is" |++| printVType vty
                               else pure () 

  checkCType : Ctx -> CType -> Expr -> Either Doc ()
  checkCType ctx cty e = do cty' <- ctypeOf ctx e 
                            if cty' /= cty 
                              then Left $ text "this expression has computation type" |++| printCType cty' |++| text "but is used as if its type is" |++| printCType cty
                              else pure ()

-- [vtype_of ctx e] computes the value type of an expression [e] in context [ctx].
-- It raises type error if [e] does not have a value type.
  vtypeOf : Ctx -> Val -> Either Doc VType
  vtypeOf ctx (Var x)       = maybe (Left $ text "unknown identifier" |++| text x) Right (lookup x ctx) 
  vtypeOf ctx (EInt _)      = pure VInt
  vtypeOf ctx (EBool _)     = pure VBool
  vtypeOf ctx (Times e1 e2) = do checkVType ctx VInt e1
                                 checkVType ctx VInt e2
                                 pure VInt
  vtypeOf ctx (Plus e1 e2)  = do checkVType ctx VInt e1
                                 checkVType ctx VInt e2
                                 pure VInt
  vtypeOf ctx (Minus e1 e2) = do checkVType ctx VInt e1
                                 checkVType ctx VInt e2
                                 pure VInt
  vtypeOf ctx (Equal e1 e2) = do checkVType ctx VInt e1
                                 checkVType ctx VInt e2
                                 pure VBool
  vtypeOf ctx (Less e1 e2)  = do checkVType ctx VInt e1
                                 checkVType ctx VInt e2
                                 pure VBool
  vtypeOf ctx (Thunk e)     = map VForget (ctypeOf ctx e)

-- [ctype_of ctx e] computes the computation type of a computation [e] in context [ctx].
-- It raises type error if [e] does not have a computation type.
  ctypeOf : Ctx -> Expr -> Either Doc CType
  ctypeOf ctx (If e1 e2 e3) = do checkVType ctx VBool e1
                                 ty <- ctypeOf ctx e2
                                 checkCType ctx ty e3
                                 pure ty
  ctypeOf ctx (Fun x ty e)  = map (CArrow ty) (ctypeOf (insert x ty ctx) e)
  ctypeOf ctx (Apply e1 e2) = do CArrow ty1 ty2 <- ctypeOf ctx e1 
                                 | ty => Left (text "this expression is used as a function but its type is" |++| printCType ty)
                                 checkVType ctx ty1 e2
                                 pure ty2
  ctypeOf ctx (Do x e1 e2)  = do CFree ty1 <- ctypeOf ctx e1 
                                 | ty => Left (text "this expression is sequenced but its type is" |++| printCType ty)
                                 ctypeOf (insert x ty1 ctx) e2
  ctypeOf ctx (Let x e1 e2) = do ty1 <- vtypeOf ctx e1
                                 ctypeOf (insert x ty1 ctx) e2
  ctypeOf ctx (Return e)    = map CFree (vtypeOf ctx e)
  ctypeOf ctx (Force e)     = do VForget ty1 <- vtypeOf ctx e 
                                 | ty => Left (text "this expression is forced but its type is" |++| printVType ty)
                                 pure ty1
  ctypeOf ctx (Rec x ty e)  = do checkCType (insert x (VForget ty) ctx) ty e
                                 pure ty
