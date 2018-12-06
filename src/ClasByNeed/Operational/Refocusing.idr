module ClasByNeed.Operational.Refocusing

import Control.Monad.Syntax
import Control.Monad.State
import ClasByNeed.Syntax
import ClasByNeed.Redex
import ClasByNeed.Operational.Decompose

%access public export
%default covering

-- An optimized interpreter that deforests `decomp . recomp k` into an
-- in-place `refocus k`.

%access public export
%default covering
    
data Result x a = FinalAnswer x (Term x a) a (MetaContext x a)
                | Stuck x (Force x a) (Demanded x a)
                | CoStuck a (Value x a) (MetaContext x a)

refocus : Eq x => MetaContext x a -> Command x a -> Decomposition x a
refocus k c = decompCommand c k

iter : (Eq a, Alternative m, MonadState (List a) m) => Decomposition a a -> m (Result a a)
iter (Answer x t a k) = pure $ FinalAnswer x t a k
iter (Need x f d)     = pure $ Stuck x f d
iter (CoNeed a v k)   = pure $ CoStuck a v k
iter (Rdx r k)        = (iter . refocus k <=< contract) r

run : (Eq a, Alternative m, MonadState (List a) m) => Command a a -> m (Result a a)                    
run = iter . refocus MEmpty
    