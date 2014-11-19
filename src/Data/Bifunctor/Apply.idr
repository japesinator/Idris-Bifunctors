module Data.Bifunctor.Apply

-- These are not Biapplicatives.  Those are in Data.Biapplicative

import Data.Bifunctor

infixl 4 <<$>>, <<.>>, <<., .>>, <<..>>

||| Primarily used to make the definitions of bilift2 and bilift3 pretty
|||
||| ````idris example
||| (<<$>>) (+) 1 2 = 3
||| ````
|||
(<<$>>) : (a -> b) -> a -> b
(<<$>>) = id

||| Biapplys (not to be confused with Biapplicatives)
||| @p The action of the Biapply on pairs of objects
class Bifunctor p => Biapply (p : Type -> Type -> Type) where

  ||| Applys a bifunctor of functions to another bifunctor of the same type
  |||
  ||| ````idris example
  ||| (reverse, (\x => x + 1)) <<.>> ("hello", 1) == ("olleh", 2)
  ||| ````
  |||
  (<<.>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Given two bifunctors, sequences them leftwards
  |||
  ||| ````idris example
  ||| ("hello", 1) <<. ("goodbye", 2) == ("hello", 1)
  ||| ````
  |||
  (<<.) : p a b -> p c d -> p a b
  a <<. b = bimap const const <<$>> a <<.>> b

  ||| Given two bifunctors, sequences them rightwards
  |||
  ||| ````idris example
  ||| ("hello", 1) <<. ("goodbye", 2) == ("goodbye", 2)
  ||| ````
  |||
  (.>>) : p a b -> p c d -> p c d
  a .>> b = bimap (const id) (const id) <<$>> a <<.>> b

||| Lifts a pair of binary functions into a bifunctor
|||
||| ````idris example
||| bilift2 (++) (+) ("hello", 1) ("goodbye", 2) == ("hellogoodbye", 3)
||| ````
|||
bilift2 : Biapply p => (a -> b -> c) -> (d -> e -> f) -> p a d -> p b e -> p c f
bilift2 f g a b = bimap f g <<$>> a <<.>> b

||| Lifts a pair of ternary functions into a bifunctor
|||
||| ````idris example
||| bilift3 (\x,y,z => x ++ (y ++ z)) (\x,y,z => x + (y + z))
|||         ("hello", 1) ("goodbye", 2) ("hello again", 3) ==
||| ("hellogoodbyehello again", 6)
||| ````
|||
bilift3 : Biapply p => (a -> b -> c -> d) -> (e -> f -> g -> h)
        -> p a e -> p b f -> p c g -> p d h
bilift3 f g a b c = bimap f g <<$>> a <<.>> b <<.>> c

||| Applies the second of two bifunctors to the first
|||
||| ````idris example
||| ("hello", 1) <<..>> (reverse, (\x => x + 1)) == ("olleh", 2)
||| ````
|||
(<<..>>): Biapply p => p a c -> p (a -> b) (c -> d) -> p b d
(<<..>>) = flip (<<.>>)

instance Biapply Pair where
  (f, g) <<.>> (a, b) = (f a, g b)
