module Main

import Control.Monad.State
import ClasByNeed.Syntax
import ClasByNeed.Operational.Run

%access public export

--let a = callcc (fn k => (I, fn x => throw k x)) 
--    f = fst a 
--    q = snd a 
--  in 
-- f q (I, I)

-- < μα. < ( I, λx.μ_. < x | α > ) | α >| ̃μa. < μβ. < a | fst · β >| ̃μf. < μδ. < a | snd · δ >| ̃μq. < f | q · ( I,I ) · tp 〉〉〉〉 

--ex2 : Command 

runMС : Command Char Char -> Maybe (Result Char Char, List Char)
runMС cmd = runStateT {m=Maybe} (run {m=StateT (List Char) Maybe} cmd) ['a', 'b', 'c']

main : IO ()
main = pure ()