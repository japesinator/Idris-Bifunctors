module Data.Bifunctor.Tannen

import Data.Bifunctor
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Tanned : (Type -> Type) -> (Type -> Type -> Type) ->
                Type -> Type -> Type where
  Tannen : (runTannen : f (p a b)) -> Tanned f p a b

instance (Bifunctor p, Functor f) => Bifunctor (Tanned f p) where
  bimap f g = Tannen . map (bimap f g) . runTannen

instance (Bifunctor p, Functor f) => Functor (Tanned f p a) where
  map f = Tannen . map (second f) . runTannen

instance (Biapplicative p, Applicative f) => Biapplicative (Tanned f p) where
  bipure a b = Tannen (pure (bipure a b))
  (Tannen fg) <<*>> (Tannen xy) = Tannen ((map (<<*>>) fg) <$> xy)

instance (Foldable f, Bifoldable p) => Bifoldable (Tanned f p) where
  bifoldMap f g = (foldr ((<+>) . (bifoldMap f g)) neutral) . runTannen

instance (Foldable f, Bifoldable p) => Foldable (Tanned f p a) where
  foldr f z t = applyEndo ((((foldr ((<+>) . (bifoldMap (const neutral)
                                                         (Endo . f))))
                                               neutral) . runTannen) t) z

instance (Traversable f, Bitraversable p) => Bitraversable (Tanned f p) where
  bitraverse f g = map Tannen . traverse (bitraverse f g) . runTannen

instance (Traversable f, Bitraversable p) => Traversable (Tanned f p a) where
  traverse f = map Tannen . traverse (bitraverse pure f) . runTannen
