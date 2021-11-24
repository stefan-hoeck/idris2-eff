module Control.Eff.State

import Control.Eff.Internal

%default total

public export
data StateL : (lbl : k) -> (s : Type) -> (a : Type) -> Type where
  [search lbl]
  Get : StateL lbl s s
  Put : (vs : s) -> StateL lbl s ()

public export
State : (s,a : Type) -> Type
State = StateL ()

export
getAt : (0 lbl : k) -> Has (StateL lbl s) fs => Eff fs s
getAt lbl = send $ Get {lbl}

export %inline
get : Has (State s) fs => Eff fs s
get = getAt ()

export
putAt : (0 lbl : k) -> Has (StateL lbl s) fs => s -> Eff fs ()
putAt lbl vs = send $ Put {lbl} vs

export %inline
put : Has (State s) fs => s -> Eff fs ()
put = putAt ()

export
modifyAt : (0 lbl : k) -> Has (StateL lbl s) fs => (s -> s) -> Eff fs ()
modifyAt lbl f = getAt lbl >>= putAt lbl . f

export %inline
modify : Has (State s) fs => (s -> s) -> Eff fs ()
modify = modifyAt ()

--------------------------------------------------------------------------------
--          Running State
--------------------------------------------------------------------------------

export
handleState :  {0 m : Type -> Type}
            -> (get : m s)
            -> (put : s -> m ())
            -> StateL lbl s a
            -> m a
handleState get _   Get      = get
handleState _   put (Put vs) = put vs

unState : (0 lbl : k) -> s -> StateL lbl s a -> (a,s)
unState _ vs Get     = (vs,vs)
unState _ _ (Put s2) = ((),s2)

export
runStateAt : (0 lbl : k)
           -> (prf : Has (StateL lbl s) fs)
           => s
           -> Eff fs t
           -> Eff (Without fs prf) (t,s)
runStateAt lbl vs fr = case toView fr of
  Pure val => pure (val,vs)
  Bind x f => case handle (unState lbl vs) x of
    Left y        => assert_total $ lift y >>= runStateAt lbl vs . f
    Right (y,vs2) => assert_total $ runStateAt lbl vs2 (f y)

export %inline
runState : (prf : Has (State s) fs)
         => s
         -> Eff fs t
         -> Eff (Without fs prf) (t,s)
runState = runStateAt ()
