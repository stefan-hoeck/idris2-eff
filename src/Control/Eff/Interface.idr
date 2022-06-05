||| Interact with Standard library

import Control.MonadRec
import Control.Monad.Free
import Data.Union
import Control.Eff.Internal

export
Has IO fs => HasIO (Free (Union fs)) where
   liftIO = send
