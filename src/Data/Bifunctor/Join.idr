module Data.Bifunctor.Join

import Data.Bifunctor
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

||| Turns a bifunctor where both arguments are the same type to a functor
|||
||| ````idris example
||| map reverse (Join ("hello, "goodbye")) == Join ("olleh", "eybdoog")
||| ````
|||
record Joined : (Type -> Type -> Type) -> Type -> Type where
  Join : (runJoined : p a a) -> Joined p a

instance Bifunctor p => Functor (Joined p) where
  map f (Join a) = Join (bimap f f a)

instance Biapplicative p => Applicative (Joined p) where
  pure a                = Join (bipure a a)
  (Join f) <$> (Join x) = Join (f <<*>> x)

instance Bifoldable p => Foldable (Joined p) where
  foldr f z (Join t) = applyEndo (bifoldMap (Endo . f) (Endo . f) t) z

instance Bitraversable p => Traversable (Joined p) where
  traverse f (Join a) = map Join (bitraverse f f a)
