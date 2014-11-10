module Data.Bifunctor.Flip

import Data.Bifunctor
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Verified.Bifunctor
import Data.Verified.Biapplicative

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

instance VerifiedBifunctor p => VerifiedBifunctor (Flipped p) where
  bifunctorIdentity (Flip x) = rewrite bifunctorIdentity x in Refl
  bifunctorComposition (Flip x) f g h i = rewrite bifunctorComposition x h i f g in Refl

instance VerifiedBiapplicative p => VerifiedBiapplicative (Flipped p) where
  biapplicativeMap (Flip x) f g = rewrite biapplicativeMap x g f in Refl
  biapplicativeIdentity (Flip x) = rewrite biapplicativeIdentity x in Refl
  biapplicativeComposition (Flip x) (Flip f) (Flip g) =
    rewrite sym (biapplicativeComposition x f g) in Refl
  biapplicativeHomomorphism x y f g = cong (biapplicativeHomomorphism y x g f)
  biapplicativeInterchange a b (Flip f) =
    rewrite biapplicativeInterchange b a f in Refl
