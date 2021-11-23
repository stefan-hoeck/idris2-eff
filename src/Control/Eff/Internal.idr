module Control.Eff.Internal

import public Control.MonadRec
import public Control.Monad.Free
import public Data.Union

%default total

||| An effectful computation yielding a value
||| of type `t` and supporting the effects listed
||| in `fs`.
public export
Eff : (fs : List (Type -> Type)) -> (t : Type) -> Type
Eff fs t = Free (Union fs) t

||| Lift a an effectful comutation into the `Eff` monad.
export
tell : Has f fs => f t -> Eff fs t
tell = lift . inj

||| Handle all effectful computations in `m`,
||| returning the underlying free monad.
export
toFree : Eff fs t -> Handler fs m -> Free m t
toFree eff h = mapK (handleAll h) eff

||| Run an effectful computation without overflowing
||| the stack by handling all computations in monad `m`.
export
runEff : MonadRec m => Eff fs t -> Handler fs m -> m t
runEff eff h = foldMap (handleAll h) eff
