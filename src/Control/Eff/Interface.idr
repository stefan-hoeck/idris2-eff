||| Interact with Standard library
module Control.Eff.Interface

import Control.MonadRec
import Control.Monad.Free
import Data.Union
import Control.Eff.Internal

export
Has IO fs => HasIO (Free (Union fs)) where
   liftIO = send


-- `Applicative` is not yet dependent
-- Please use `lift` manually

-- bindr : Subset fs0 fs2 => Subset fs1 fs2 => Eff fs0 a -> (a -> Eff fs1 b) -> Eff fs2 b
-- bindr fr fval = do
--    a <- lift fr
--    lift (fval a)

-- export
-- join : Subset fs0 fs2 => Subset fs1 fs2 => Eff fs0 (Eff fs1 a) -> Eff fs2 a
-- join @{s0} @{s1} fr = do
--    a <- lift @{s0} fr
--    lift @{s1} a

-- export
-- (>>=) : Subset fs0 fs2 => Subset fs1 fs2 => Eff fs0 a -> (a -> Eff fs1 b) -> Eff fs2 b
-- (>>=) = bindr
