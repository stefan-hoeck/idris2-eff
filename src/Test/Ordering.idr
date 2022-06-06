import Control.Eff

data Alice a = MkAlice
data Bob a = MkBob

f0 : Eff [Alice, Bob] ()
f0 = do
   send $ MkAlice
   send $ MkBob

f1 : Eff [Bob, Alice] ()
f1 = do
   f0