module Data.Bifoldable

import Data.Morphisms

%access public export

-- Idris' standard library doesn't define dual monads, and those are really
--   handy for bifoldl, so they need to be rewritten
--   {{{

record Dual a where
  constructor ToDual
  getDual : a

implementation Semigroup s => Semigroup (Dual s) where
  (ToDual a) <+> (ToDual b) = ToDual (b <+> a)

implementation Monoid s => Monoid (Dual s) where
  neutral = ToDual neutral

--   }}}

||| Bifoldables
interface Bifoldable (p : Type -> Type -> Type) where

  ||| Combine the elements of a structure using a monoid
  |||
  ||| ```idris example
  ||| bifold ("hello", "world") == "hello world"
  ||| ```
  |||
  bifold : Monoid m => p m m -> m
  bifold = bifoldMap id id

  ||| Combines the elements of a structure to a common monoid
  |||
  ||| ```idris example
  ||| bifoldMap show id (42, "hello") == "42hello"
  ||| ```
  |||
  bifoldMap : Monoid m => (a -> m) -> (b -> m) -> (p a b) -> m
  bifoldMap f g = bifoldr ((<+>) . f) ((<+>) . g) neutral

  ||| Combines the elements of a structure in a right-associative manner
  |||
  ||| ```idris example
  ||| bifoldr (++) ((++) . show) "hello" ("world", 42) == "helloworld42"
  ||| ```
  |||
  bifoldr : (a -> c -> c) -> (b -> c -> c) -> c -> p a b -> c
  bifoldr f g z t = applyEndo (bifoldMap (Endo . f) (Endo . g) t) z

  ||| Combines the elements of a structure in a left-associative manner
  |||
  ||| ```idris example
  ||| bifoldl (++) (\a,b => a ++ show b) "hello" ("world", 42) == "hello42world"
  ||| ```
  |||
  bifoldl : (c -> a -> c) -> (c -> b -> c) -> c -> p a b -> c
  bifoldl f g z t = applyEndo (getDual $ bifoldMap (ToDual . Endo . flip f)
                                                   (ToDual . Endo . flip g) t) z

||| Right associative monadic bifold
|||
||| ```idris example
||| bifoldrM (\a,b => Just $ a ++ b)
|||          (\a,b => Just $ show a ++ b) "hello" ("world", 42)
||| == Just "42worldhello"
||| ```
|||
bifoldrM : (Bifoldable t, Monad m) => (a -> c -> m c) -> (b -> c -> m c) -> c ->
                                      t a b -> m c
bifoldrM f g z0 xs = bifoldl f' g' pure xs z0 where
  f' k x z = f x z >>= k
  g' k x z = g x z >>= k

||| Left associative monadic bifold
|||
||| ```idris example
||| bifoldlM (\a,b => Just $ a ++ b)
|||          (\a,b => Just $ a ++ show b) "hello" ("world", 42)
||| == Just "hello42world"
||| ```
|||
bifoldlM : (Bifoldable t, Monad m) => (a -> b -> m a) -> (a -> c -> m a) -> a ->
                                      t b c -> m a
bifoldlM f g z0 xs = bifoldr f' g' pure xs z0 where
  f' x k z = f z x >>= k
  g' x k z = g z x >>= k

||| Traverses a structure with a pair of functions ignoring the results
|||
||| ```idris example
||| bitraverse_ Just Just ("hello", 42) == Just ()
||| ```
|||
bitraverse_ : (Bifoldable t, Applicative f) => (a -> f _) ->
                                               (b -> f _) -> t a b -> f ()
bitraverse_ f g = bifoldr ((*>) . f) ((*>) . g) $ pure ()

||| Evaluate a pair of pair of functions for each element of a structure,
||| ignoring the results.
||| Like bitraverse_ but with the arguments flipped
|||
||| ```idris example
||| bitraverse_ Just Just ("hello", 42) == Just ()
||| ```
|||
bifor_ : (Bifoldable t, Applicative f) => (a -> f _) ->
                                          (b -> f _) -> t a b -> f ()
bifor_ f g = bifoldr ((*>) . f) ((*>) . g) $ pure ()

||| Map a pair of monadic actions onto a structure, ignoring the results
|||
||| ```idris example
||| bimapM_ Just Just ("hello", 42) == Just ()
||| ```
|||
bimapM_ : (Bifoldable t, Monad m) => (a -> m _) -> (b -> m _) -> t a b -> m ()
bimapM_ f g = bifoldr ((. const) . (>>=) . f)
                      ((. const) . (>>=) . g) $ pure ()

||| Evaluate a pair of monadic actions on each element in a structure, ignoring
||| the results.
||| Like bimapM_ but with the arguments flipped
|||
||| ```idris example
||| bimapM_ ("hello", 42) Just Just == Just ()
||| ```
|||
biforM_ : (Bifoldable t, Monad m) => t a b -> (a -> m _) -> (b -> m _) -> m ()
biforM_ p f g = bimapM_ f g p

||| Sequences the actions in a structure, ignoring the results
|||
||| ```idris example
||| bisequence_ (Just "hello", Just "world") == Just ()
||| ```
|||
bisequence_ : (Bifoldable t, Applicative f) => t (f a) (f b) -> f ()
bisequence_ = bifoldr (*>) (*>) $ pure ()

||| Collects all the elements of a structure into a list
|||
||| ```idris example
||| biList ("hello", "world") == ["hello", "world"]
||| ```
|||
biList : Bifoldable t => t a a -> List a
biList = bifoldr (::) (::) []

||| Reduces a structure of lists to a single list
|||
||| ```idris example
||| biconcat ([1,2],[3,4]) == [1,2,3,4]
||| ```
|||
biconcat : Bifoldable t => t (List a) (List a) -> List a
biconcat = bifold

||| Reduces a structure to a list given methods to do so
|||
||| ```idris example
||| biconcatMap (\x => [x]) (\x => [show x]) ("hello", 42) == ["hello", "42"]
||| ```
|||
biconcatMap : Bifoldable t => (a -> (List c)) ->
                              (b -> (List c)) -> t a b -> List c
biconcatMap = bifoldMap

-- As in `Dual`, we need records not present in the standard library
--   {{{

record Any where
  constructor ToAny
  getAny : Bool

implementation Semigroup Any where
  (ToAny a) <+> (ToAny b) = ToAny (a || b)

implementation Monoid Any where
  neutral = ToAny False

record All where
  constructor ToAll
  getAll : Bool

implementation Semigroup All where
  (ToAll a) <+> (ToAll b) = ToAll (a && b)

implementation Monoid All where
  neutral = ToAll True

--   }}}

||| Checks if any elements in a structure satisfy a given condition
|||
||| ```idris example
||| biany ((==) "42") ((==) 42) ("hello", 42) == True
||| ```
|||
biany : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biany p q = getAny . bifoldMap (ToAny . p) (ToAny . q)

||| Checks if all elements in a structure satisfy a given condition
|||
||| ```idris example
||| biall ((==) "42") ((==) 42) ("hello", 42) == False
||| ```
|||
biall : Bifoldable t => (a -> Bool) -> (b -> Bool) -> t a b -> Bool
biall p q = getAll . bifoldMap (ToAll . p) (ToAll . q)

implementation Bifoldable Pair where
  bifoldMap f g (a, b) = f a <+> g b

implementation Bifoldable Either where
  bifoldMap f g = either f g
