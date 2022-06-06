module Data.Union

import Data.Subset

%default total

||| A list of effect handlers handling effects of types `fs`
||| wrapping results in type `m`.
public export
data Handler : (fs : List (Type -> Type)) -> (m : Type -> Type) -> Type where
  Nil : Handler [] m
  (::) : (h : forall x . f x -> m x) -> Handler fs m -> Handler (f :: fs) m

||| Sum type holding a value of type `t` wrapped in one of the
||| effect types listed in `fs`.
public export
data Union : (fs : List (Type -> Type)) -> (t : Type) -> Type where
  U : (ix : Has f fs) -> (val : f t) -> Union fs t

public export
Uninhabited (Union [] t) where
  uninhabited (U ix v) = absurd ix

||| Inject an effectful computation into a `Union`.
public export %inline
inj : (prf : Has f fs) => f t -> Union fs t
inj = U prf

||| Tries to extract an effect from a `Union`.
public export
prj : (prf : Has f fs) => Union fs t -> Maybe (f t)
prj {prf = Z}    (U Z v)     = Just v
prj {prf = S ix} (U (S x) v) = prj {prf = ix} (U x v)
prj _                        = Nothing

||| Extracts the last effect from a unary sum.
public export
prj1 : Union [f] t -> f t
prj1 (U Z val) = val
prj1 (U (S x) val) impossible

||| Handles all remaining effects via the given
||| (heterogeneous) list of event handlers.
public export
handleAll : Handler fs m -> Union fs t -> m t
handleAll []       y              = absurd y
handleAll (h :: t) (U Z val)     = h val
handleAll (h :: t) (U (S y) val) = handleAll t (U y val)

||| Prepend a new effect to an existing `Union` value.
public export
weaken : Union fs a -> Union (f :: fs) a
weaken (U ix val) = U (S ix) val

-- public export
-- weakenN : Subset fs fs' => Union fs a -> Union fs' a
-- weakenN @{subset} (U ix val) = U (lemma_subset subset ix) val

||| Handle on of the effects in a `Union`. Unlike in other
||| effect libraries, it's not necessary that the effect
||| is the first in the list. To improve type inference,
||| the return type is calculated from the `prf` value.
public export
decomp :  (prf : Has f fs)
       => Union fs a
       -> Either (Union (fs - f) a) (f a)
decomp {prf = Z}                      (U Z     val) = Right $ val
decomp {prf = Z}                      (U (S x) val) = Left $ U x val
decomp {prf = S y} {fs = f :: h :: t} (U Z val)     = Left $ U Z val
decomp {prf = S y} {fs = f :: h :: t} (U (S x) val) =
  mapFst weaken $ decomp (U x val)

||| Handle one of the effects in a `Union`. Unlike in other
||| effect libraries, it's not necessary that the effect
||| is the first in the list. To improve type inference,
||| the return type is calculated from the `prf` value.
public export
handle :  (prf : Has f fs)
       => (f a -> res)
       -> Union fs a
       -> Either (Union (fs - f) a) res
handle g = map g . decomp
