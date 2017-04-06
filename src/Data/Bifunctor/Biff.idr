module Data.Bifunctor.Biff

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

%access public export

||| Compose two Functors on the inside of a Bifunctor
|||
||| ````idris example
||| Biff (Just 1, the (List String) ["hello"])
||| ````
|||
record Biffed (p : Type -> Type -> Type) (f : Type -> Type) (g : Type -> Type)
              a b where
  constructor Biff
  runBiff : p (f a) (g b)

implementation (Bifunctor p, Functor f, Functor g) => Bifunctor (Biffed p f g) where
  bimap f g = Biff . bimap (map f) (map g) . runBiff

implementation (Bifunctor p, Functor g) => Functor (Biffed p f g a) where
  map f = Biff . second (map f) . runBiff

implementation (Biapplicative p, Applicative f, Applicative g) =>
         Biapplicative (Biffed p f g) where
  bipure a b                = Biff $ bipure (pure a) (pure b)
  (Biff fg) <<*>> (Biff xy) = Biff $ bimap (<*>) (<*>) fg <<*>> xy

implementation (Bifoldable p, Foldable f, Foldable g) =>
         Bifoldable (Biffed p f g) where
  bifoldMap f g = bifoldMap (concatMap f) (concatMap g) . runBiff

implementation (Bifoldable p, Foldable f, Foldable g) =>
         Foldable (Biffed p f g a) where
  foldr = bifoldr (flip const)

implementation (Bitraversable p, Traversable f, Traversable g) =>
         Bitraversable (Biffed p f g) where
  bitraverse f g = map Biff . bitraverse (traverse f) (traverse g) . runBiff

implementation (Bitraversable p, Traversable f, Traversable g) =>
         Traversable (Biffed p f g a) where
  traverse f = map Biff . bitraverse pure (traverse f) . runBiff
