module Control.Eff.Internal

import public Control.MonadRec
import public Control.Monad.Free
import public Data.Union
import public Data.Subset

%default total

||| An effectful computation yielding a value
||| of type `t` and supporting the effects listed
||| in `fs`.
public export
Eff : (fs : List (Type -> Type)) -> (t : Type) -> Type
Eff fs = Free (Union fs)

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
            => (a -> Eff (fs - f) b)
            -> (forall v . f v -> (v -> Eff (fs - f) b) -> Eff (fs - f) b)
            -> Eff fs a
            -> Eff (fs - f) b
handleRelay fval fcont fr = case toView fr of
  Pure val => fval val
  Bind x g => case decomp {prf} x of
    Left y  => assert_total $ lift y >>= handleRelay fval fcont . g
    Right y => assert_total $ fcont y (handleRelay fval fcont . g)

export handle :  (prf : Has f fs)
              => (forall v . f v -> (resume: v -> Eff (fs - f) b) -> Eff (fs - f) b)
              -> Eff fs b
              -> Eff (fs - f) b
handle fcont fr = handleRelay pure fcont fr

export
handleRelayS :  (prf : Has f fs)
             => s
             -> (s -> a -> Eff (fs - f) b)
             -> (forall v . s -> f v -> (s -> v -> Eff (fs - f) b) -> Eff (fs - f) b)
             -> Eff fs a
             -> Eff (fs - f) b
handleRelayS vs fval fcont fr = case toView fr of
  Pure val => fval vs val
  Bind x g => case decomp {prf} x of
    Left y  => assert_total $ lift y >>= handleRelayS vs fval fcont . g
    Right y => assert_total $ fcont vs y (\vs2 => handleRelayS vs2 fval fcont . g)


||| Turn effect monad into a more relaxed one. Can be used to reorder effects as well. See src/Test/Ordering.idr for usage.
export
lift : Subset fs fs' => Eff fs a -> Eff fs' a
lift @{s} fr = case toView fr of
  Pure val => pure val
  Bind x g => do
    let mx = weaken @{s} x
    freex <- lift mx
    lift (assert_smaller fr (g freex))

