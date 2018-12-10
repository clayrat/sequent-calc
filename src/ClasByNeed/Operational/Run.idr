module ClasByNeed.Operational.Run

import Control.Monad.Syntax
import Control.Monad.State
import ClasByNeed.Syntax
import ClasByNeed.Redex
import ClasByNeed.Result
import ClasByNeed.Operational.Decompose

%access public export
%default covering

-- An iterative interpreter implementing the small-step operational semantics
-- for l_[lv]

iter : (Eq a, Alternative m, MonadState (List a) m) => Decomposition a a -> m (ResultM a a)
iter (Answer x t a k) = pure $ FinalAnswerM x t a k
iter (Need x f d)     = pure $ StuckM x f d
iter (CoNeed a v k)   = pure $ CoStuckM a v k
iter (Rdx r k)        = (iter . decomp . recomp k <=< contract) r
                
run : (Eq a, Alternative m, MonadState (List a) m) => Command a a -> m (ResultM a a)                    
run = iter . decomp
