module Control.Eff.Except

import Control.Eff.Internal

%default total

public export
data ExceptL : (lbl : k) -> (err : Type) -> (a : Type) -> Type where
  [search lbl]
  Err : err -> ExceptL lbl err a

public export
Except : (err,a : Type) -> Type
Except = ExceptL ()

public export
FailL : (lbl : k) -> (a : Type) -> Type
FailL lbl = ExceptL lbl ()

public export
Fail : (a : Type) -> Type
Fail = FailL ()

export
throwAt : (0 lbl : k) -> Has (ExceptL lbl err) fs => err -> Eff fs a
throwAt lbl e = send $ Err {lbl} e

export %inline
throw : Has (Except err) fs => err -> Eff fs a
throw = throwAt ()

export %inline
failAt : (0 lbl : k) -> Has (FailL lbl) fs => Eff fs a
failAt lbl = throwAt lbl ()

export %inline
fail : Has Fail fs => Eff fs a
fail = throwAt () ()

export %inline
rethrowAt : (0 lbl : k) -> Has (ExceptL lbl err) fs => Either err a -> Eff fs a
rethrowAt lbl = either (throwAt lbl) pure

export %inline
rethrow : Has (Except err) fs => Either err a -> Eff fs a
rethrow = rethrowAt ()

export %inline
noteAt :  (0 lbl : k)
       -> Has (ExceptL lbl err) fs
       => Lazy err
       -> Maybe a
       -> Eff fs a
noteAt lbl e = maybe (throwAt lbl e) pure

export %inline
note : Has (Except err) fs => Lazy err -> Maybe a -> Eff fs a
note = noteAt ()

export %inline
fromJustAt : (0 lbl : k) -> Has (FailL lbl) fs => Maybe a -> Eff fs a
fromJustAt lbl = noteAt lbl ()

export %inline
fromJust : Has Fail fs => Maybe a -> Eff fs a
fromJust = fromJustAt ()

--------------------------------------------------------------------------------
--          Handling Exceptions
--------------------------------------------------------------------------------

unExcept : ExceptL lbl err a -> err
unExcept (Err e) = e

export
catchAt :  (0 lbl : k)
        -> Has (ExceptL lbl err) fs
        => (err -> Eff (fs - ExceptL lbl err) a)
        -> Eff fs a
        -> Eff (fs - ExceptL lbl err) a
catchAt _ f = handleRelay pure $ \v,_ => f (unExcept v)

export %inline
catch :  Has (Except err) fs
      => (err -> Eff (fs - Except err) a)
      -> Eff fs a
      -> Eff (fs - Except err) a
catch = catchAt ()

export
runExceptAt :  (0 lbl : k)
            -> Has (ExceptL lbl err) fs
            => Eff fs a
            -> Eff (fs - ExceptL lbl err) (Either err a)
runExceptAt _ = handleRelay (pure . Right) $ \v,_ => pure (Left $ unExcept v)

export %inline
runExcept :  Has (Except err) fs
          => Eff fs a
          -> Eff (fs - Except err) (Either err a)
runExcept = runExceptAt ()

export
runFailAt :  (0 lbl : k)
          -> Has (FailL lbl) fs
          => Eff fs a
          -> Eff (fs - FailL lbl) (Maybe a)
runFailAt lbl = map (either (const Nothing) Just) . runExceptAt lbl

export %inline
runFail : Has Fail fs => Eff fs a -> Eff (fs - Fail) (Maybe a)
runFail = runFailAt ()
