module Control.Eff.Writer

import Control.Eff.Internal

%default total

public export
data WriterL : (lbl : k) -> (w : Type) -> (a : Type) -> Type where
  [search lbl]
  Tell : (vw : w) -> WriterL lbl w ()

public export
Writer : (w,a : Type) -> Type
Writer = WriterL ()

export
tellAt : (0 lbl : k) -> Has (WriterL lbl w) fs => w -> Eff fs ()
tellAt lbl vw = send $ Tell {lbl} vw

export %inline
tell : Has (Writer w) fs => w -> Eff fs ()
tell = tellAt ()

--------------------------------------------------------------------------------
--          Running Writer
--------------------------------------------------------------------------------

export
handleWriter :  {0 m : Type -> Type}
             -> (tell : w -> m ())
             -> WriterL lbl w a
             -> m a
handleWriter tell (Tell vw) = tell vw

unWriter : (0 lbl : k) -> u -> (u -> w -> u) -> WriterL lbl w a -> (a,u)
unWriter _ vu f (Tell vw) = ((), f vu vw)

export
foldWriterAt : (0 lbl : k)
             -> (prf : Has (WriterL lbl w) fs)
             => u
             -> (u -> w -> u)
             -> Eff fs t
             -> Eff (Without fs prf) (t,u)
foldWriterAt lbl vu acc fr = case toView fr of
  Pure val => pure (val,vu)
  Bind x f => case handle (unWriter lbl vu acc) x of
    Left y        => assert_total $ lift y >>= foldWriterAt lbl vu acc . f
    Right (y,vu2) => assert_total $ foldWriterAt lbl vu2 acc (f y)

export %inline
foldWriter : (prf : Has (Writer w) fs)
           => u
           -> (u -> w -> u)
           -> Eff fs t
           -> Eff (Without fs prf) (t,u)
foldWriter = foldWriterAt ()

export
runWriterAt : (0 lbl : k)
            -> (prf : Has (WriterL lbl w) fs)
            => Monoid w
            => Eff fs t
            -> Eff (Without fs prf) (t,w)
runWriterAt lbl = foldWriterAt lbl neutral (<+>)

export %inline
runWriter :  (prf : Has (Writer w) fs)
          => Monoid w
          => Eff fs t
          -> Eff (Without fs prf) (t,w)
runWriter = runWriterAt ()
