import Control.Eff

data Alice a = MkAlice
data Bob a = MkBob
data Charles a = MkCharles

f0 : Eff [Alice, Bob] ()
f0 = do
   send $ MkAlice
   send $ MkBob

f1 : Eff [Bob, Alice] ()
f1 = do
   lift f0 -- reorder

f2 : Eff [Alice, Bob, Charles] ()
f2 = lift f1
