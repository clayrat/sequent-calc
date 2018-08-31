module Levy.Eval

import Data.SortedMap
import Text.PrettyPrint.WL
import Levy.Syntax

%access public export
%default total

-- An efficient interpreter.

mutual
  Env : Type
  Env = SortedMap Name Value

  data Value = VInt Integer 
             | VBool Bool
             | VThunk Env Expr
             | VFun Env Name Expr
             | VReturn Value

printValue : Value -> Doc 
printValue (VInt k)     = integer k
printValue (VBool b)    = bool b
printValue (VThunk _ _) = text "<thunk>"
printValue (VFun _ _ _) = text "<fun>"
printValue (VReturn v)  = text "return" |++| parens (printValue v)

mutual 
  comp : Env -> Expr -> Either Doc Value
  comp env (Fun x _ e)    = pure $ VFun env x e
  comp env (If e1 e2 e3)  = do VBool b <- expr env e1 
                               | _ => Left (text "boolean expected")
                               if b then comp env e2 
                                    else comp env e3
  comp env (Apply e1 e2)  = do VFun env' x e <- comp env e1 
                               | _ => Left (text "function expected")
                               v2 <- expr env e2
                               assert_total $ comp (insert x v2 env') e
  comp env (Let x e1 e2)  = do v <- expr env e1
                               comp (insert x v env) e2
  comp env (Do x e1 e2)   = do VReturn v <- comp env e1  
                               | _ => Left (text "return expected")
                               comp (insert x v env) e2
  comp env (Return e)     = map VReturn (expr env e)
  comp env (Force e)      = do VThunk env e <- expr env e 
                               | _ => Left (text "thunk expected in force")
                               comp env e
  comp env e@(Rec x _ e') = comp (insert x (VThunk env e) env) e'
  
  expr : Env -> Val -> Either Doc Value
  expr env (Var x)       = maybe (Left $ text "unknown variable" |++| text x) Right (lookup x env)
  expr env (EInt k)      = pure $ VInt k
  expr env (EBool b)     = pure $ VBool b
  expr env (Thunk e)     = pure $ VThunk env e
  expr env (Times e1 e2) = do v1 <- expr env e1
                              v2 <- expr env e2
                              case (v1, v2) of 
                                (VInt k1, VInt k2) => pure $ VInt (k1 * k2)
                                _ => Left $ text "integers expected in multiplication"
  expr env (Plus e1 e2)  = do v1 <- expr env e1
                              v2 <- expr env e2
                              case (v1, v2) of 
                                (VInt k1, VInt k2) => pure $ VInt (k1 + k2)
                                _ => Left $ text "integers expected in addition"
  expr env (Minus e1 e2) = do v1 <- expr env e1
                              v2 <- expr env e2
                              case (v1, v2) of 
                                (VInt k1, VInt k2) => pure $ VInt (k1 - k2)
                                _ => Left $ text "integers expected in subtraction"
  expr env (Equal e1 e2) = do v1 <- expr env e1
                              v2 <- expr env e2
                              case (v1, v2) of 
	                            (VInt k1, VInt k2) => pure $ VBool (k1 == k2)
	                            _ => Left $ text "integers expected in ="
  expr env (Less e1 e2) = do v1 <- expr env e1
                             v2 <- expr env e2
                             case (v1, v2) of 
                               (VInt k1, VInt k2) => pure $ VBool (k1 < k2)
                               _ => Left $ text "integers expected in <"
