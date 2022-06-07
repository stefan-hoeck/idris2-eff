||| Interact with Standard library
module Control.Eff.Interface

import Control.MonadRec
import Control.Monad.Free
import Data.Union
import Control.Eff.Internal

export
Has IO fs => HasIO (Free (Union fs)) where
   liftIO = send

export
Has f fs => Cast (f t) (Eff fs t) where
  cast = send

export
Subset fs fs' => Cast (Eff fs a) (Eff fs' a) where
  cast = lift
