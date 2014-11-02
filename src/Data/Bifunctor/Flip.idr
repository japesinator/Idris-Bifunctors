module Data.Bifunctor.Flip

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Flip : (Type -> Type -> Type) -> Type -> Type -> Type where
  toFlip : (runFlip : p a b) -> Flip p b a

instance Bifunctor p => Bifunctor (Flip p) where
  bimap f g = toFlip . bimap g f . runFlip

instance Bifunctor p => Functor (Flip p a) where
  map f = toFlip . first f . runFlip

instance Biapply p => Biapply (Flip p) where
  (toFlip fg) <<.>> (toFlip xy) = toFlip (fg <<.>> xy)

instance Biapplicative p => Biapplicative (Flip p) where
  bipure a b                    = toFlip $ bipure b a
  (toFlip fg) <<*>> (toFlip xy) = toFlip (fg <<*>> xy)

instance Bifoldable p => Bifoldable (Flip p) where
  bifoldMap f g = bifoldMap g f . runFlip

instance Bitraversable p => Bitraversable (Flip p) where
  bitraverse f g = map toFlip . bitraverse g f . runFlip
