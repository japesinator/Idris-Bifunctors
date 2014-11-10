module Data.Bifunctor.Joker

import Data.Bifunctor
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Joked : (Type -> Type) -> Type -> Type -> Type where
  Joker : (runJoker : p b) -> Joked p a b

instance Functor f => Bifunctor (Joked f) where
  bimap _ g = Joker . map g . runJoker

instance Functor f => Functor (Joked f b) where
  map g = Joker . map g . runJoker

instance Applicative f => Biapplicative (Joked f) where
  bipure _ b                = Joker (pure b)
  (Joker a) <<*>> (Joker b) = Joker (a <$> b)

instance Foldable t => Bifoldable (Joked t) where
  bifoldMap _ g = concatMap g . runJoker

instance Foldable t => Foldable (Joked t a) where
  foldr f z (Joker t) = foldr f z t

instance Traversable t => Bitraversable (Joked t) where
  bitraverse _ g = map Joker . traverse g . runJoker

instance Traversable t => Traversable (Joked t a) where
  traverse g = map Joker . traverse g . runJoker
