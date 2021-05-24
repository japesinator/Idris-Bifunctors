module Data.Bifunctor.Join

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

||| Turns a Bifunctor where both arguments are the same type to a Functor
|||
||| ````idris example
||| map reverse (Join ("hello, "goodbye")) == Join ("olleh", "eybdoog")
||| ````
|||
public export
record Joined (p : Type -> Type -> Type) (a : Type) where
  constructor Join
  runJoined : p a a

public export
implementation Bifunctor p => Functor (Joined p) where
  map f (Join a) = Join $ bimap f f a

public export
implementation Biapplicative p => Applicative (Joined p) where
  pure a                = Join $ bipure a a
  (Join f) <*> (Join x) = Join $ f <<*>> x

public export
implementation Bifoldable p => Foldable (Joined p) where
  foldr f z = bifoldr f f z . runJoined

public export
implementation Bitraversable p => Traversable (Joined p) where
  traverse f (Join a) = map Join $ bitraverse f f a
