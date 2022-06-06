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


||| Removes an element from a list. This is used to
||| calculate the list of effects after a single effect
||| was properly handled.
public export
0 (-) : (ts : List a) -> (v : a) -> (prf : Has v ts) => List a
(-) (x :: vs)      x {prf = Z}   = vs
(-) (y :: x :: xs) v {prf = S k} = y :: (-) (x :: xs) v


-- public export
-- 0 lemma_minus : {0 w : a} -> ((-) {prf=Z} (w :: vs) w) = vs
-- lemma_minus = Refl


-- -- lemma_replace_0 : Has f ((-) {a} (w :: vs) w) -> Has f vs
-- -- lemma_replace_0 : Has {a} f ((-) {a} ((::) {a} w vs) w {prf = S {{a:839} = a} {w} {v = w} {vs} a}) -> Has {a} f vs

-- public export
-- weaken : {0 w : a} -> {0 fs' : List a} -> {e : Has {a} w fs'} -> Has {a} f ((-) {a} fs' w {prf = e}) -> Has {a} f fs'
-- weaken {e=Z} Z = S Z
-- weaken {e=Z} (S b) = S (S b)
-- weaken {e=S a} {w} b =
--   replace {p=(\x => Has f (w :: x))} (lemma_minus {w}) (S b)
  

||| Proof that one set is subset of another set.
||| Sets are represented by `List`.
public export
data Subset : {0 a: Type} -> (xs, ys : List a) -> Type where
  Nil : Subset [] ys
  (::) : {0 x: a} -> (e : Has x ys) -> Subset xs (ys - x) -> Subset (x::xs) ys

-- public export
-- lemma_subset : Subset fs fs' -> Has f fs -> Has f fs'
-- lemma_subset Nil has0 impossible
-- lemma_subset (e :: subset) Z = e
-- lemma_subset (e :: subset) (S has) = 
--   let has' = lemma_subset subset has in
--   weaken has'
