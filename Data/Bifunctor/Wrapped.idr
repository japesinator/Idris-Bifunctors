module Data.Bifunctor.Wrapped

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms
import Data.Verified.Bifunctor

||| Wrap a Bifunctor
|||
||| ````idris example
||| Wrap ("hello", 1)
||| ````
|||
public export
record Wrapped (p : Type -> Type -> Type) a b where
  constructor Wrap
  unwrap : p a b

public export
implementation Bifunctor p => Bifunctor (Wrapped p) where
  bimap f g = Wrap . bimap f g . unwrap

public export
implementation Bifunctor p => Functor (Wrapped p a) where
  map f = Wrap . mapSnd f . unwrap

public export
implementation Biapply p => Biapply (Wrapped p) where
  (Wrap fg) <<.>> (Wrap xy) = Wrap (fg <<.>> xy)

public export
implementation Biapplicative p => Biapplicative (Wrapped p) where
  bipure a b                = Wrap $ bipure a b
  (Wrap fg) <<*>> (Wrap xy) = Wrap $ fg <<*>> xy

public export
implementation Bifoldable p => Bifoldable (Wrapped p) where
  bifoldMap f g = bifoldMap f g . unwrap

public export
implementation Bifoldable p => Foldable (Wrapped p a) where
  foldr f z = bifoldr (const $ const z) f z . unwrap

public export
implementation Bitraversable p => Bitraversable (Wrapped p) where
  bitraverse f g = map Wrap . bitraverse f g . unwrap

public export
implementation Bitraversable p => Traversable (Wrapped p a) where
  traverse f = map Wrap . bitraverse pure f . unwrap

public export
implementation VerifiedBifunctor p => VerifiedBifunctor (Wrapped p) where
  bifunctorIdentity (Wrap x) = bifunctorIdentity (Wrap x)
  bifunctorComposition (Wrap x) f g h i =
    rewrite bifunctorComposition x f g h i in Refl
