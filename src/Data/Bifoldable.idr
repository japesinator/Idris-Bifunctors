module Data.Bifoldable

import Data.Morphisms

-- Idris' standard library doesn't define dual monads, and those are really
--   handy for bifoldl, so they need to be rewritten
--   {{{

record Dual : Type -> Type where
  toDual : (getDual : a) -> Dual a

instance Semigroup s => Semigroup (Dual s) where
  (toDual a) <+> (toDual b) = toDual (b <+> a)

instance Monoid s => Monoid (Dual s) where
  neutral = toDual neutral

--   }}}

||| Bifoldables
||| @p a structure with two varieties of objects that can be folded across
class Bifoldable (p : Type -> Type -> Type) where

  ||| Combines the elements of a structure to a common monoid
  |||
  ||| ````idris example
  ||| bifoldMap show id (1, "hello") == "1hello"
  ||| ````
  |||
  bifoldMap : Monoid m => (a -> m) -> (b -> m) -> (p a b) -> m
  bifoldMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

  ||| Combines the elements of a structure in a right-associative manner
  |||
  ||| ````idris example
  ||| bifoldr (\x,y => (show x) ++ y) (++) "" (1, "hello") == "hello1"
  ||| ````
  |||
  bifoldr : (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c
  bifoldr f g z t = applyEndo (bifoldMap (Endo . f) (Endo . g) t) z

  ||| Combines the elements of a structure in a left-associative manner
  |||
  ||| ````idris example
  ||| bifoldl (\x,y => (show x) ++ y) (++) "" (1, "hello") == "hello1"
  ||| ````
  |||
  bifoldl : (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c
  bifoldl f g z t = applyEndo (getDual (bifoldMap (toDual . Endo . flip f)
                                                  (toDual . Endo . flip g) t)) z

||| Combine to elements of a structure using a monoid
|||
||| ````idris example
||| bifold ("hello", "goodbye") == "hellogoodbye"
||| ````
|||
bifold : (Bifoldable t, Monoid m) => t m m -> m
bifold = bifoldMap id id

||| Right associative monadic bifold
|||
||| ````idris example
||| bifoldrM (\x,y => Just ((show x) ++ y))
|||          (\x,y => Just (x        ++ y)) "" (1, "hello") == Just "hello1"
||| ````
|||
bifoldrM : (Bifoldable t, Monad m) => (a -> c -> m c) -> (b -> c -> m c) -> c -> t a b -> m c
bifoldrM f g z0 xs = bifoldl f' g' return xs z0 where
  f' k x z = f x z >>= k
  g' k x z = g x z >>= k

||| Left associative monadic bifold
|||
||| ````idris example
||| bifoldlM (\x,y => Just (x ++ (show y)))
|||          (\x,y => Just (x ++ y       )) "" (1, "hello") == Just "hello1"
||| ````
|||
bifoldlM : (Bifoldable t, Monad m) => (a -> b -> m a) -> (a -> c -> m a) -> a -> t b c -> m a
bifoldlM f g z0 xs = bifoldr f' g' return xs z0 where
  f' x k z = f z x >>= k
  g' x k z = g z x >>= k

||| Traverses a structure with a functions ignoring the results
|||
||| ````idris example
||| bitraverse_ Just Just (1, "hello") = Just ()
||| ````
|||
bitraverse_ : (Bifoldable t, Applicative f) => (a -> f c) ->
                                               (b -> f d) -> t a b -> f ()
bitraverse_ f g = bifoldr (($>) . f) (($>) . g) (pure ())

||| Map a monad onto a structure, ignoring the results
|||
||| ````idris example
||| bimapM_ Just Just (1, "hello") = Just ()
||| ````
|||
bimapM_ : (Bifoldable t, Monad m) => (a -> m c) -> (b -> m d) -> t a b -> m ()
bimapM_ f g = bifoldr ((\x, y => (x >>= (\_ => y))) . f)
                      ((\x, y => (x >>= (\_ => y))) . g) (return ())

||| Sequences the actions in a structure, ignoring the results
|||
||| ````idris example
||| bisequence_ (Just "hello", Just 1) == Just ()
||| ````
|||
bisequence_ : (Bifoldable t, Applicative f) => t (f a) (f b) -> f ()
bisequence_ = bifoldr ($>) ($>) (pure ())

||| Collects all the elements of a structure into a list
|||
||| ````idris example
||| bilist (1, 2) == [2, 1]
||| ````
|||
biList : Bifoldable t => t a a -> List a
biList = bifoldr (::) (::) []

||| Reduces a structure of lists to a single list
|||
||| ````idris example
||| biconcat ([1], [2]) == [1,2]
||| ````
|||
biconcat : Bifoldable t => t (List a) (List a) -> List a
biconcat = bifold

||| Reduces a structure to a list given methods to do so
biconcatMap : Bifoldable t => (a -> (List c)) ->
                              (b -> (List c)) -> t a b -> List c
biconcatMap = bifoldMap

-- As in `Dual`, we need records not present in the standard library
--   {{{

record Any : Type where
  toAny : (getAny : Bool) -> Any

instance Semigroup Any where
  (toAny a) <+> (toAny b) = toAny (a || b)

instance Monoid Any where
  neutral = toAny False

record All : Type where
  toAll : (getAll : Bool) -> All

instance Semigroup All where
  (toAll a) <+> (toAll b) = toAll (a && b)

instance Monoid All where
  neutral = toAll True

--   }}}

||| Checks if any elements in a structure satisfy a given condition
|||
||| ````idris example
||| biany ((==) 42) ((==) "goodbye world") testPair0 == True
||| ````
|||
biany : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biany p q = getAny . bifoldMap (toAny . p) (toAny . q)

||| Checks if all elements in a structure satisfy a given condition
|||
||| ````idris example
||| biall ((==) 42) ((==) "goodbye world") testPair0 == False
||| ````
|||
biall : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biall p q = getAll . bifoldMap (toAll . p) (toAll . q)

instance Bifoldable Pair where
  bifoldMap f g (a, b) = f a <+> g b

instance Bifoldable Either where
  bifoldMap f _ (Left a)  = f a
  bifoldMap _ g (Right b) = g b
