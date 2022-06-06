||| Interact with Standard library
module Control.Eff.Interface

import Control.Monad.Free
import Data.Union
import Control.Eff.Internal

export
Has IO fs => HasIO (Free (Union fs)) where
   liftIO = send

-- (>>=) : Eff fs0 a -> (a -> Eff fs1 b) -> Eff (fs0 + fs1) b
