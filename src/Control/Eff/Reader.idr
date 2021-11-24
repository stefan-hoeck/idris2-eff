module Control.Eff.Reader

import Control.Eff.Internal

%default total

public export
data ReaderL : (lbl : k) -> (env : Type) -> (a : Type) -> Type where
  [search lbl]
  Ask : ReaderL lbl env env

public export
Reader : (env,a : Type) -> Type
Reader = ReaderL ()

export
askAt : (0 lbl : k) -> Has (ReaderL lbl env) fs => Eff fs env
askAt lbl = tell $ Ask {lbl}

export %inline
ask : Has (Reader env) fs => Eff fs env
ask = askAt ()

export %inline
asksAt : (0 lbl : k) -> Has (ReaderL lbl env) fs => (env -> a) -> Eff fs a
asksAt lbl f = f <$> askAt lbl

export %inline
asks : Has (Reader env) fs => (env -> a) -> Eff fs a
asks f = f <$> ask

--------------------------------------------------------------------------------
--          Running Reader
--------------------------------------------------------------------------------

export
handleReader :  {0 m : Type -> Type}
             -> m env
             -> ReaderL lbl env a
             -> m a
handleReader x Ask = x

unReader : (0 lbl : k) -> env -> ReaderL lbl env a -> a
unReader _ ve Ask = ve

export
runReaderAt : (0 lbl : k)
            -> (prf : Has (ReaderL lbl env) fs)
            => env
            -> Eff fs t
            -> Eff (Without fs prf) t
runReaderAt lbl ve fr = case toView fr of
  Pure val => pure val
  Bind x f => case handle (unReader lbl ve) x of
    Left y  => assert_total $ lift y >>= runReaderAt lbl ve . f
    Right y => assert_total $ runReaderAt lbl ve (f y)

export %inline
runReader : (prf : Has (Reader env) fs)
          => env -> Eff fs t -> Eff (Without fs prf) t
runReader = runReaderAt ()
