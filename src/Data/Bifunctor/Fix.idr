module Data.Bifunctor.Fix

import Data.Biapplicative
import Data.Bifoldable
import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Bitraversable
import Data.Morphisms

%access public export

record Fix (p : Type -> Type -> Type) a where
  constructor In
  out : p (Fix p a) a

implementation Bifunctor p => Functor (Fix p) where
  map f (In p) = assert_total . In $ bimap (map f) f p

implementation Biapplicative p => Applicative (Fix p) where
  pure a            = assert_total . In $ bipure (pure a) a
  (In p) <*> (In q) = assert_total . In $ biliftA2 (<*>) id p q

implementation Bifoldable p => Foldable (Fix p) where
  foldr f z = let f' = Endo . f in
    assert_total . flip applyEndo z . bifoldMap (concatMap f') f' . out

implementation Bitraversable p => Traversable (Fix p) where
  traverse f = assert_total . map In . bitraverse (traverse f) f . out
