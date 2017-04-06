module Data.Bifunctor.Clown

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

%access public export

||| Make a Functor over just the first argument of a Bifunctor
||| Intuitively, C_l_owns to the left, Joke_r_s to the right
record Clowned (p : Type -> Type) a b where
  constructor Clown
  runClown : p a

implementation Functor f => Bifunctor (Clowned f) where
  bimap f = const $ Clown . map f . runClown

implementation Functor (Clowned f a) where
  map = const $ Clown . runClown

implementation Applicative f => Biapplicative (Clowned f) where
  bipure                    = const . Clown . pure
  (Clown a) <<*>> (Clown b) = Clown $ a <*> b

implementation Foldable t => Bifoldable (Clowned t) where
  bifoldMap f = const $ concatMap f . runClown

implementation Foldable (Clowned f a) where
  foldr = const const

implementation Traversable t => Bitraversable (Clowned t) where
  bitraverse f = const $ map Clown . traverse f . runClown

implementation Traversable (Clowned t a) where
  traverse = const $ pure . Clown . runClown
