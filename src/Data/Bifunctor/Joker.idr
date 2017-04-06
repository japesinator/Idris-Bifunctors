module Data.Bifunctor.Joker

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

%access public export

||| Make a Functor over just the second argument of a Bifunctor
||| Intuitively, Joke_r_s to the right, C_l_owns to the left
record Joked (p : Type -> Type) a b where
  constructor Joker
  runJoker : p b

implementation Functor f => Bifunctor (Joked f) where
  bimap _ g = Joker . map g . runJoker

implementation Functor f => Functor (Joked f b) where
  map g = Joker . map g . runJoker

implementation Applicative f => Biapplicative (Joked f) where
  bipure                    = const $ Joker . pure
  (Joker a) <<*>> (Joker b) = Joker $ a <*> b

implementation Foldable t => Bifoldable (Joked t) where
  bifoldMap _ g = concatMap g . runJoker

implementation Foldable t => Foldable (Joked t a) where
  foldr f z = foldr f z . runJoker

implementation Traversable t => Bitraversable (Joked t) where
  bitraverse _ g = map Joker . traverse g . runJoker

implementation Traversable t => Traversable (Joked t a) where
  traverse g = map Joker . traverse g . runJoker
