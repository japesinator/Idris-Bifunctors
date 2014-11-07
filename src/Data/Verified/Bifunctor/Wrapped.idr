module Data.Verified.Bifunctor.Wrapped

import Data.Bifunctor.Wrapped
import Data.Verified.Bifunctor

instance VerifiedBifunctor p => VerifiedBifunctor (Wrapped p) where
  bifunctorIdentity (Wrap x) = rewrite bifunctorIdentity x in Refl
  bifunctorComposition (Wrap x) f g h i =
    rewrite bifunctorComposition x f g h i in Refl
