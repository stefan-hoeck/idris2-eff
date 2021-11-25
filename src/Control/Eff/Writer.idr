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

unWriter : u -> (u -> w -> u) -> WriterL lbl w a -> (a,u)
unWriter vu f (Tell vw) = ((), f vu vw)

export
foldWriterAt :  (0 lbl : k)
             -> Has (WriterL lbl w) fs
             => u
             -> (u -> w -> u)
             -> Eff fs t
             -> Eff (fs - WriterL lbl w) (t,u)
foldWriterAt _ vu acc =
  handleRelayS vu (\x,y => pure (y,x)) $ \vu2,w,f =>
    let (vv,vu3) = unWriter vu2 acc w
     in f vu3 vv

export %inline
foldWriter :  Has (Writer w) fs
           => u
           -> (u -> w -> u)
           -> Eff fs t
           -> Eff (fs - Writer w) (t,u)
foldWriter = foldWriterAt ()

export
runWriterAt :  (0 lbl : k)
            -> Has (WriterL lbl w) fs
            => Monoid w
            => Eff fs t
            -> Eff (fs - WriterL lbl w) (t,w)
runWriterAt lbl = foldWriterAt lbl neutral (<+>)

export %inline
runWriter : Has (Writer w) fs => Monoid w =>
            Eff fs t -> Eff (fs - Writer w) (t,w)
runWriter = runWriterAt ()
