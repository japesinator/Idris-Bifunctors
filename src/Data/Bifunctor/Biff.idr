module Data.Bifunctor.Biff

import Data.Bifunctor
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Biffed : (Type -> Type -> Type) -> (Type -> Type) -> (Type -> Type) ->
                Type -> Type -> Type where
  Biff : (runBiff : p (f a) (g b)) -> Biffed p f g a b

instance (Bifunctor p, Functor f, Functor g) => Bifunctor (Biffed p f g) where
  bimap f g = Biff . bimap (map f) (map g) . runBiff

instance (Bifunctor p, Functor g) => Functor (Biffed p f g a) where
  map f = Biff . second (map f) . runBiff

instance (Biapplicative p, Applicative f, Applicative g) =>
         Biapplicative (Biffed p f g) where
  bipure a b                = Biff (bipure (pure a) (pure b))
  (Biff fg) <<*>> (Biff xy) = Biff (bimap (<$>) (<$>) fg <<*>> xy)

instance (Bifoldable p, Foldable f, Foldable g) =>
         Bifoldable (Biffed p f g) where
  bifoldMap f g = bifoldMap (foldr ((<+>) . f) neutral)
                            (foldr ((<+>) . g) neutral) . runBiff


instance (Bifoldable p, Foldable f, Foldable g) =>
         Foldable (Biffed p f g a) where
  foldr f z t = bifoldr (flip const) f z t

instance (Bitraversable p, Traversable f, Traversable g) =>
         Bitraversable (Biffed p f g) where
  bitraverse f g = map Biff . bitraverse (traverse f) (traverse g) . runBiff

instance (Bitraversable p, Traversable f, Traversable g) =>
         Traversable (Biffed p f g a) where
  traverse f = map Biff . bitraverse pure (traverse f) . runBiff
