module Data.Bifunctor.Join

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable

record Join : (Type -> Type -> Type) -> Type -> Type where
  toJoin : (runJoin : p a a) -> Join p a

instance Bifunctor p => Functor (Join p) where
  map f (toJoin a) = toJoin (bimap f f a)

instance Biapplicative p => Applicative (Join p) where
  pure a                    = toJoin (bipure a a)
  (toJoin f) <$> (toJoin x) = toJoin (f <<*>> x)
