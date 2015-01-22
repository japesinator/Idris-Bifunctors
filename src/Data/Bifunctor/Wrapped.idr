module Data.Bifunctor.Wrapped

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms
import Data.Verified.Bifunctor
import Data.Verified.Biapplicative

||| Wrap a Bifunctor
|||
||| ````idris example
||| Wrap ("hello", 1)
||| ````
|||
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

instance Bifoldable p => Foldable (Wrapped p a) where
  foldr f z (Wrap t) = applyEndo (bifoldMap (const neutral) (Endo . f) t) z

instance Bitraversable p => Bitraversable (Wrapped p) where
  bitraverse f g = map Wrap . bitraverse f g . unwrap

instance Bitraversable p => Traversable (Wrapped p a) where
  traverse f = map Wrap . bitraverse pure f . unwrap

instance VerifiedBifunctor p => VerifiedBifunctor (Wrapped p) where
  bifunctorIdentity (Wrap x) = rewrite bifunctorIdentity x in Refl
  bifunctorComposition (Wrap x) f g h i =
    rewrite bifunctorComposition x f g h i in Refl

instance VerifiedBiapplicative p => VerifiedBiapplicative (Wrapped p) where
  biapplicativeMap (Wrap x) f g = rewrite biapplicativeMap x f g in Refl
  biapplicativeIdentity (Wrap x) = rewrite biapplicativeIdentity x in Refl
  biapplicativeComposition (Wrap x) (Wrap f) (Wrap g) =
    rewrite sym (biapplicativeComposition x f g) in Refl
  biapplicativeHomomorphism x y f g = cong (biapplicativeHomomorphism x y f g)
  biapplicativeInterchange a b (Wrap f) =
    rewrite biapplicativeInterchange a b f in Refl
