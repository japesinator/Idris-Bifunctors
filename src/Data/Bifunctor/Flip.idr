module Data.Bifunctor.Flip

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

%access public export

record Flip (p : Type -> Type -> Type) b a where
  constructor ToFlip
  runFlip : p a b

instance Bifunctor p => Bifunctor (Flip p) where
  bimap f g = ToFlip . bimap g f . runFlip

instance Bifunctor p => Functor (Flip p a) where
  map f = ToFlip . first f . runFlip

instance Biapply p => Biapply (Flip p) where
  (ToFlip fg) <<.>> (ToFlip xy) = ToFlip $ fg <<.>> xy

instance Biapplicative p => Biapplicative (Flip p) where
  bipure a b                    = ToFlip $ bipure b a
  (ToFlip fg) <<*>> (ToFlip xy) = ToFlip $ fg <<*>> xy

instance Bifoldable p => Bifoldable (Flip p) where
  bifoldMap f g = bifoldMap g f . runFlip

instance Bitraversable p => Bitraversable (Flip p) where
  bitraverse f g = map ToFlip . bitraverse g f . runFlip
