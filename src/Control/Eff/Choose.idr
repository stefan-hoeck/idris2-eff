module Control.Eff.Choose

import Control.Eff.Internal

%default total

public export
data Choose : (a : Type) -> Type where
  Empty : Choose a
  Alt   : (lft, rgt : a) -> Choose a

export %inline
empty : Has Choose fs => Eff fs a
empty = send Empty

export %inline
alt : Has Choose fs => Eff fs a -> Eff fs a -> Eff fs a
alt x y = join $ send (Alt x y)

export %inline
guard : Has Choose fs => Bool -> Eff fs ()
guard False = empty
guard True  = pure ()

--------------------------------------------------------------------------------
--          Running Choose
--------------------------------------------------------------------------------

export
runChoose :  Alternative f
          => (p : Has Choose fs)
          => Eff fs a
          -> Eff (Without fs p) (f a)
runChoose fr = case toView fr of
  Pure val => pure (pure val)
  Bind x g => case handle (id {a = Choose _}) x of
    Left y  => assert_total $ lift y >>= runChoose . g
    Right Empty         => pure empty
    Right (Alt lft rgt) => assert_total $ do
      x <- runChoose (g lft)
      y <- runChoose (g rgt)
      pure (x <|> y)
