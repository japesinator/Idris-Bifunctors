module Data.Bifunctor.Flip

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Flipped : (Type -> Type -> Type) -> Type -> Type -> Type where
  Flip : (runFlip : p a b) -> Flipped p b a

instance Bifunctor p => Bifunctor (Flipped p) where
  bimap f g = Flip . bimap g f . runFlip

instance Bifunctor p => Functor (Flipped p a) where
  map f = Flip . first f . runFlip

instance Biapply p => Biapply (Flipped p) where
  (Flip fg) <<.>> (Flip xy) = Flip (fg <<.>> xy)

instance Biapplicative p => Biapplicative (Flipped p) where
  bipure a b                = Flip $ bipure b a
  (Flip fg) <<*>> (Flip xy) = Flip (fg <<*>> xy)

instance Bifoldable p => Bifoldable (Flipped p) where
  bifoldMap f g = bifoldMap g f . runFlip

instance Bifoldable p => Foldable (Flipped p a) where
  foldr f z (Flip t) = applyEndo (bifoldMap (Endo . f) (const neutral) t) z

instance Bitraversable p => Bitraversable (Flipped p) where
  bitraverse f g = map Flip . bitraverse g f . runFlip

instance Bitraversable p => Traversable (Flipped p a) where
  traverse f = map Flip . bitraverse f pure . runFlip
