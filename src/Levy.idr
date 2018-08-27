module Main

import Data.SortedMap
import Text.PrettyPrint.WL

import TParsec
import TParsec.Running

import Levy.Syntax
import Levy.Lexer
import Levy.Parser
import Levy.TypeCheck
import Levy.Eval

%access public export
%default total

RunEnv : Type
RunEnv = (Ctx, Env)

exec : RunEnv -> TopLevelCmd -> IO RunEnv
exec (ctx, env) (TLExpr e)  = 
  do case ctypeOf ctx e of 
      Left err => putStrLn $ toString err
      Right ty => 
        case comp env e of 
          Left err => putStrLn $ toString err
          Right v => putStrLn $ (toString $ printValue v) ++ " : " ++ (toString $ printCType ty)
     pure (ctx, env)

exec (ctx, env) (TLDef n e) =
  do case vtypeOf ctx e of 
       Left err => 
         do putStrLn $ toString err
            pure (ctx, env)
       Right ty => 
         case expr env e of 
           Left err => 
             do putStrLn $ toString err
                pure (ctx, env)
           Right v => 
             do putStrLn $ "val " ++ n ++ " : " ++ (toString $ printVType ty) ++ " = " ++ (toString $ printValue v)
                pure (insert n ty ctx, insert n v env)

partial
main : IO ()           
main = do 
  [_, fnam] <- getArgs | _ => putStrLn "wrong args"
  Right prog <- readFile fnam | Left err => printLn err  
  case parseMaybe prog file of 
    Just p => 
      do foldlM exec (SortedMap.empty, SortedMap.empty) p
         pure ()
    Nothing => putStrLn "parse error"