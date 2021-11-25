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
send : Has f fs => f t -> Eff fs t
send = lift . inj

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

||| Extract the (pure) result of an effectful computation
||| where all effects have been handled.
export
extract : Eff [] a -> a
extract fr = case toView fr of
  Pure val => val
  Bind u _ => absurd u

export
handleRelay :  (prf : Has f fs)
            => (a -> Eff (Without fs prf) b)
            -> (forall v . f v -> (v -> Eff (Without fs prf) b) -> Eff (Without fs prf) b)
            -> Eff fs a
            -> Eff (Without fs prf) b
handleRelay fval fcont fr = case toView fr of
  Pure val => fval val
  Bind x g => case decomp {prf} x of
    Left y  => assert_total $ lift y >>= handleRelay fval fcont . g
    Right y => assert_total $ fcont y (handleRelay fval fcont . g)


