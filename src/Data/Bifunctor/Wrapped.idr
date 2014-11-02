module Data.Bifunctor.Wrapped

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Wrapped : (Type -> Type -> Type) -> Type -> Type -> Type where
  Wrap : (unwrap : p a b) -> Wrapped p a b

instance Bifunctor p => Bifunctor (Wrapped p) where
  bimap f g = Wrap . bimap f g . unwrap

instance Bifunctor p => Functor (Wrapped p a) where
  map f = Wrap . second f . unwrap

instance Biapply p => Biapply (Wrapped p) where
  (Wrap fg) <<.>> (Wrap xy) = Wrap (fg <<.>> xy)

instance Biapplicative p => Biapplicative (Wrapped p) where
  bipure a b                = Wrap $ bipure a b
  (Wrap fg) <<*>> (Wrap xy) = Wrap (fg <<*>> xy)

instance Bifoldable p => Bifoldable (Wrapped p) where
  bifoldMap f g = bifoldMap f g . unwrap

instance Bitraversable p => Bitraversable (Wrapped p) where
  bitraverse f g = map Wrap . bitraverse f g . unwrap
