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
record Joined (p : Type -> Type -> Type) a where
  constructor Join
  runJoined : p a a

instance Bifunctor p => Functor (Joined p) where
  map f (Join a) = Join (bimap f f a)

instance Biapplicative p => Applicative (Joined p) where
  pure a                = Join (bipure a a)
  (Join f) <*> (Join x) = Join (f <<*>> x)

instance Bifoldable p => Foldable (Joined p) where
  foldr f z (Join t) = applyEndo (bifoldMap (Endo . f) (Endo . f) t) z

instance Bitraversable p => Traversable (Joined p) where
  traverse f (Join a) = map Join (bitraverse f f a)
