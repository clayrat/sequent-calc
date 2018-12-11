module ClasByNeed.Concrete.Result

import ClasByNeed.Concrete.Syntax
import ClasByNeed.Concrete.Redex

%access public export
%default total

data MetaContext x a = MEmpty
                     | MLet (MetaContext x a) a (Command x a) x

data ResultM x a = FinalAnswerM x (Term x a) a (MetaContext x a)
                 | StuckM x (Force x a) (Demanded x a)
                 | CoStuckM a (Value x a) (MetaContext x a)                 

data ResultE x a = FinalAnswerE x (Term x a) a (Environment x a)
                 | StuckE x (Force x a) (Environment x a)
                 | CoStuckE a (Value x a) (Environment x a)
