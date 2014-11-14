module Data.Biapplicative

import Data.Bifunctor
import Data.Bifunctor.Apply

infixl 4 <<*>>, <<*, *>>, <<**>>

||| Biapplicatives
||| @p the action of the biapplicative on pairs of objects
class Bifunctor p => Biapplicative (p : Type -> Type -> Type) where

  ||| Lifts two values into a biapplicative
  |||
  ||| ````idris example
  ||| bipure 1 "hello" = (1, "hello")
  ||| ````
  |||
  bipure : a -> b -> p a b

  ||| Applies a biapplicative of functions to a second biapplicative
  |||
  ||| ````idris example
  ||| ( (\x => x + 1), reverse ) <<*>> (1, "hello") == (2, "olleh")
  ||| ````
  |||
  (<<*>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Sequences two biapplicatives rightwards
  |||
  ||| ````idris example
  ||| (1, "hello") *>> (2, "goodbye") = (2, "goodbye")
  ||| ````
  |||
  (*>>) : p a b -> p c d -> p c d
  a *>> b = bimap (const id) (const id) <<$>> a <<*>> b

  ||| Sequences two biapplicatives leftwards
  |||
  ||| ````idris example
  ||| (1, "hello") <<* (2, "goodbye") = (1, "hello")
  ||| ````
  |||
  (<<*) : p a b -> p c d -> p a b
  a <<* b = bimap const const <<$>> a <<*>> b

||| Applies the second of two biapplicatives to the first
|||
||| ````idris example
||| (1, "hello") <<**>> ( (\x => x + 1), reverse ) == (2, "olleh")
||| ````
|||
(<<**>>) : Biapplicative p => p a c -> p (a -> b) (c -> d) -> p b d
(<<**>>) = flip (<<*>>)

instance Biapplicative Pair where
  bipure a b = (a, b)
  (f, g) <<*>> (a, b) = (f a, g b)
