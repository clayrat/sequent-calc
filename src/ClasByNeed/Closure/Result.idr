module ClasByNeed.Closure.Result

import ClasByNeed.Closure.Syntax

%default total
%access public export

data ResultE x a = FinalAnswerE x (Term x a) a (Environment x a)
                 | StuckE x (Force x a) (Environment x a)
                 | CoStuckE a (Value x a) (Environment x a)
         