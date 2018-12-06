module ClasByNeed.Identifier

import Control.Monad.Syntax
import Control.Monad.State

%default total
%access public export

pop : Alternative m => List a -> m (a, List a)
pop []      = empty
pop (x::xs) = pure (x, xs)

fresh : (Alternative m, MonadState (List a) m) => m a
fresh = do (x,xs) <- pop =<< get
           put xs
           pure x
