module Data.Subset

%default total

||| Proof that a value is present in a list. This is
||| isomorphic to `Data.List.Elem` but with (in my opinion)
||| more fitting names for our use case.
public export
data Has : (v : a) -> (ts : List a) -> Type where
  Z : Has v (v :: vs)
  S : Has v vs -> Has v (w :: vs)


export
Uninhabited (Has v []) where
  uninhabited Z impossible
  uninhabited (S _) impossible


public export
lemma_has_single : Has f [x] -> x = f
lemma_has_single Z = Refl


public export
drop : (ts : List a) -> Has v ts -> List a
drop (x :: xs)  Z    = xs
drop (x :: xs) (S k) = x :: drop xs k


||| Removes an element from a list. This is used to
||| calculate the list of effects after a single effect
||| was properly handled.
public export
(-) : (ts : List a) -> (v : a) -> (prf : Has v ts) => List a
(-) xs _ {prf} = drop xs prf


||| Proof that one set is subset of another set.
||| Sets are represented by `List`. There is no gaurantee for no duplicate in list though.
public export
data Subset : {0 a: Type} -> (xs, ys : List a) -> Type where
  Nil : Subset [] ys
  (::) : {0 x: a} -> (e : Has x ys) -> Subset xs ys -> Subset (x::xs) ys


public export
lemma_subset : Subset fs fs' -> Has f fs -> Has f fs'
lemma_subset Nil has0 impossible
lemma_subset (e :: _     ) Z = e
lemma_subset (_ :: subset) (S has) = lemma_subset subset has
