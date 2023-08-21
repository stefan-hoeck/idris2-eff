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
askAt lbl = send $ Ask {lbl}

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
handleReader :
     {0 m : Type -> Type}
  -> m env
  -> ReaderL lbl env a
  -> m a
handleReader x Ask = x

unReader : env -> ReaderL lbl env a -> a
unReader ve Ask = ve

export
runReaderAt :
     (0 lbl : k)
  -> {auto _ : Has (ReaderL lbl env) fs}
  -> env
  -> Eff fs t
  -> Eff (fs - ReaderL lbl env) t
runReaderAt _ ve = handleRelay pure $ \v,f => f (unReader ve v)

export %inline
runReader : Has (Reader env) fs => env -> Eff fs t -> Eff (fs - Reader env) t
runReader = runReaderAt ()
