module Data.Bifunctor.Clown

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

||| Make a Functor over just the first argument of a Bifunctor
record Clowned : (Type -> Type) -> Type -> Type -> Type where
  Clown : (runClown : p a) -> Clowned p a b

instance Functor f => Bifunctor (Clowned f) where
  bimap f _ = Clown . map f . runClown

instance Functor (Clowned f a) where
  map _ = Clown . runClown

instance Applicative f => Biapplicative (Clowned f) where
  bipure a _                = Clown (pure a)
  (Clown a) <<*>> (Clown b) = Clown (a <*> b)

instance Foldable t => Bifoldable (Clowned t) where
  bifoldMap f _ = concatMap f . runClown

instance Foldable (Clowned f a) where
  foldr _ z _ = z

instance Traversable t => Bitraversable (Clowned t) where
  bitraverse f _ = map Clown . traverse f . runClown

instance Traversable (Clowned t a) where
  traverse _ = pure . Clown . runClown
