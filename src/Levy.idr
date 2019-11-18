module Main

import TParsec
import TParsec.Running

import Data.SortedMap
import Text.PrettyPrint.WL

import Levy.Syntax
import Levy.Lexer
import Levy.Parser
import Levy.TypeCheck
import Levy.Eval

%access public export
%default total

RunEnv : Type
RunEnv = (Ctx, Env)

Show Doc where
  show = toString

exec : RunEnv -> TopLevelCmd -> IO RunEnv
exec (ctx, env) (TLExpr e)  =
  do case ctypeOf ctx e of
       Left err => printLn err
       Right ty =>
         case comp env e of
           Left err => printLn err
           Right v => printLn $ printValue v |++| text ":" |++| printCType ty
     pure (ctx, env)

exec (ctx, env) (TLDef n v) =
  case vtypeOf ctx v of
     Left err =>
       do printLn err
          pure (ctx, env)
     Right ty =>
       case expr env v of
         Left err =>
           do printLn err
              pure (ctx, env)
         Right vl =>
           do printLn $ text "val" |++| text n |++| text ":" |++| printVType ty |++| text "=" |++| printValue vl
              pure (insert n ty ctx, insert n vl env)

partial
main : IO ()
main =
  do [_, fnam] <- getArgs | _ => putStrLn "wrong args"
     Right prog <- readFile fnam | Left err => printLn err
     case parseMaybe prog file of
      Just p => foldlM exec (SortedMap.empty, SortedMap.empty) p *> pure ()
      Nothing => putStrLn "parse error"