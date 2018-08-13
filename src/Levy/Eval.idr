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
  comp env (Fun x _ e) = pure $ VFun env x e
  comp env (If e1 e2 e3) = do v <- expr env e1
                              case v of 
                                VBool True => comp env e2
                                VBool False => comp env e3
                                _ => Left $ text "boolean expected"
  comp env (Apply e1 e2) = do v <- comp env e1
                              case v of
                                VFun env' x e => do v2 <- expr env e2
                                                    assert_total $ comp (insert x v2 env') e
                                _ => Left $ text "function expected"
  comp env (Let x e1 e2) = do v <- expr env e1
                              comp (insert x v env) e2
  comp env (Do x e1 e2) = do c <- comp env e1 
                             case c of 
                               VReturn v => comp (insert x v env) e2
                               _ => Left $ text "return expected"
  comp env (Return e) = do v <- expr env e
                           pure $ VReturn v
  comp env (Force e) = do c <- expr env e 
                          case c of 
  	                        VThunk env e => comp env e
  	                        _ => Left $ text "thunk expected in force"
  comp env e@(Rec x _ e') = comp (insert x (VThunk env e) env) e'
  comp env  _ = Left $ text "computation expected"
  
  expr : Env -> Expr -> Either Doc Value
  expr env (Var x) = maybe (Left $ text "unknown variable" |++| text x) Right (lookup x env)
  expr env (EInt k) = pure $ VInt k
  expr env (EBool b) = pure $ VBool b
  expr env (Thunk e) = pure $ VThunk env e
  expr env (Times e1 e2) = do v1 <- expr env e1
                              v2 <- expr env e2
                              case (v1, v2) of 
                                (VInt k1, VInt k2) => pure $ VInt (k1 * k2)
                                _ => Left $ text "integers expected in multiplication"
  expr env (Plus e1 e2) = do v1 <- expr env e1
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
  expr env _ = Left $ text "expression expected"
