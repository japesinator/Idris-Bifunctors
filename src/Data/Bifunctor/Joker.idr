module Data.Bifunctor.Joker

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

||| Make a Functor over just the second argument of a Bifunctor
record Joked (p : Type -> Type) a b where
  constructor Joker
  runJoker : p b

instance Functor f => Bifunctor (Joked f) where
  bimap _ g = Joker . map g . runJoker

instance Functor f => Functor (Joked f b) where
  map g = Joker . map g . runJoker

instance Applicative f => Biapplicative (Joked f) where
  bipure _ b                = Joker (pure b)
  (Joker a) <<*>> (Joker b) = Joker (a <*> b)

instance Foldable t => Bifoldable (Joked t) where
  bifoldMap _ g = concatMap g . runJoker

instance Foldable t => Foldable (Joked t a) where
  foldr f z = foldr f z . runJoker

instance Traversable t => Bitraversable (Joked t) where
  bitraverse _ g = map Joker . traverse g . runJoker

instance Traversable t => Traversable (Joked t a) where
  traverse g = map Joker . traverse g . runJoker
