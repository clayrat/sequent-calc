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
  checkVType : Ctx -> VType -> Expr -> Either Doc ()
  checkVType ctx vty e = do vty' <- vtypeOf ctx e
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
  vtypeOf : Ctx -> Expr -> Either Doc VType
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
  vtypeOf ctx (Thunk e)     = do ty <- ctypeOf ctx e
                                 pure $ VForget ty
  vtypeOf ctx  _            = Left $ text "a value was expected but a computation was encountered"

-- [ctype_of ctx e] computes the computation type of a computation [e] in context [ctx].
-- It raises type error if [e] does not have a computation type.
  ctypeOf : Ctx -> Expr -> Either Doc CType
  ctypeOf ctx (If e1 e2 e3) = do checkVType ctx VBool e1
                                 ty <- ctypeOf ctx e2
                                 checkCType ctx ty e3
                                 pure ty
  ctypeOf ctx (Fun x ty e)  = do ty2 <- ctypeOf (insert x ty ctx) e 
                                 pure $ CArrow ty ty2
  ctypeOf ctx (Apply e1 e2) = do ct <- ctypeOf ctx e1 
                                 case ct of
                                   CArrow ty1 ty2 => do checkVType ctx ty1 e2
                                                        pure ty2
                                   ty => Left $ text "this expression is used as a function but its type is" |++| printCType ty
  ctypeOf ctx (Do x e1 e2)  = do ct <- ctypeOf ctx e1 
                                 case ct of 
                                   CFree ty1 => ctypeOf (insert x ty1 ctx) e2
                                   ty => Left $ text "this expression is sequenced but its type is" |++| printCType ty
  ctypeOf ctx (Let x e1 e2) = do ty1 <- vtypeOf ctx e1
                                 ctypeOf (insert x ty1 ctx) e2
  ctypeOf ctx (Return e)    = do ty <- vtypeOf ctx e
                                 pure $ CFree ty
  ctypeOf ctx (Force e)     = do vt <- vtypeOf ctx e 
                                 case vt of 
                                   VForget ty => pure ty
                                   ty => Left $ text "this expression is forced but its type is" |++| printVType ty
  ctypeOf ctx (Rec x ty e)  = do checkCType (insert x (VForget ty) ctx) ty e
                                 pure ty
  ctypeOf ctx  _            = Left $ text "a computation was expected but a value was encountered"
