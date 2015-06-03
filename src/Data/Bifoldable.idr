module Data.Bifoldable

import Data.Morphisms

-- Idris' standard library doesn't define dual monads, and those are really
--   handy for bifoldl, so they need to be rewritten
--   {{{

record Dual a where
  constructor toDual
  getDual : a

instance Semigroup s => Semigroup (Dual s) where
  (toDual a) <+> (toDual b) = toDual (b <+> a)

instance Monoid s => Monoid (Dual s) where
  neutral = toDual neutral

--   }}}

||| Bifoldables
||| @p a structure with two varieties of objects that can be folded across
class Bifoldable (p : Type -> Type -> Type) where

  ||| Combine the elements of a structure using a monoid
  bifold : Monoid m => p m m -> m
  bifold = bifoldMap id id

  ||| Combines the elements of a structure to a common monoid
  bifoldMap : Monoid m => (a -> m) -> (b -> m) -> (p a b) -> m
  bifoldMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

  ||| Combines the elements of a structure in a right-associative manner
  bifoldr : (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c
  bifoldr f g z t = applyEndo (bifoldMap (Endo . f) (Endo . g) t) z

  ||| Combines the elements of a structure in a left-associative manner
  bifoldl : (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c
  bifoldl f g z t = applyEndo (getDual $ bifoldMap (toDual . Endo . flip f)
                                                   (toDual . Endo . flip g) t) z

||| Right associative monadic bifold
bifoldrM : (Bifoldable t, Monad m) => (a -> c -> m c) -> (b -> c -> m c) -> c ->
                                      t a b -> m c
bifoldrM f g z0 xs = bifoldl f' g' return xs z0 where
  f' k x z = f x z >>= k
  g' k x z = g x z >>= k

||| Left associative monadic bifold
bifoldlM : (Bifoldable t, Monad m) => (a -> b -> m a) -> (a -> c -> m a) -> a ->
                                      t b c -> m a
bifoldlM f g z0 xs = bifoldr f' g' return xs z0 where
  f' x k z = f z x >>= k
  g' x k z = g z x >>= k

||| Traverses a structure with a functions ignoring the results
bitraverse_ : (Bifoldable t, Applicative f) => (a -> f c) ->
                                               (b -> f d) -> t a b -> f ()
bitraverse_ f g = bifoldr ((*>) . f) ((*>) . g) $ pure ()

||| Map a monad onto a structure, ignoring the results
bimapM_ : (Bifoldable t, Monad m) => (a -> m c) -> (b -> m d) -> t a b -> m ()
bimapM_ f g = bifoldr ((\x, y => (x >>= (\_ => y))) . f)
                      ((\x, y => (x >>= (\_ => y))) . g) $ return ()

||| Sequences the actions in a structure, ignoring the results
bisequence_ : (Bifoldable t, Applicative f) => t (f a) (f b) -> f ()
bisequence_ = bifoldr (*>) (*>) $ pure ()

||| Collects all the elements of a structure into a list
biList : Bifoldable t => t a a -> List a
biList = bifoldr (::) (::) []

||| Reduces a structure of lists to a single list
biconcat : Bifoldable t => t (List a) (List a) -> List a
biconcat = bifold

||| Reduces a structure to a list given methods to do so
biconcatMap : Bifoldable t => (a -> (List c)) ->
                              (b -> (List c)) -> t a b -> List c
biconcatMap = bifoldMap

-- As in `Dual`, we need records not present in the standard library
--   {{{

record Any where
  constructor toAny
  getAny : Bool

instance Semigroup Any where
  (toAny a) <+> (toAny b) = toAny (a || b)

instance Monoid Any where
  neutral = toAny False

record All where
  constructor toAll
  getAll : Bool

instance Semigroup All where
  (toAll a) <+> (toAll b) = toAll (a && b)

instance Monoid All where
  neutral = toAll True

--   }}}

||| Checks if any elements in a structure satisfy a given condition
biany : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biany p q = getAny . bifoldMap (toAny . p) (toAny . q)

||| Checks if all elements in a structure satisfy a given condition
biall : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biall p q = getAll . bifoldMap (toAll . p) (toAll . q)

instance Bifoldable Pair where
  bifoldMap f g (a, b) = f a <+> g b

instance Bifoldable Either where
  bifoldMap f _ (Left a)  = f a
  bifoldMap _ g (Right b) = g b
