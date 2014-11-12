module Data.Biapplicative

import Data.Bifunctor
import Data.Bifunctor.Apply

infixl 4 <<*>>, <<*, *>>, <<**>>

||| Biapplicatives
||| @p the action of the biapplicative on pairs of objects
class Bifunctor p => Biapplicative (p : Type -> Type -> Type) where

  ||| Lifts two values into a biapplicative
  bipure : a -> b -> p a b

  ||| Applies a biapplicative of functions to a second biapplicative
  (<<*>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Given two biapplicatives, returns the second
  (*>>) : p a b -> p c d -> p c d
  a *>> b = bimap (const id) (const id) <<$>> a <<*>> b

  ||| Given two biapplicatives, returns the first
  (<<*) : p a b -> p c d -> p a b
  a <<* b = bimap const const <<$>> a <<*>> b

||| Applies the second of two biapplicatives to the first
(<<**>>) : Biapplicative p => p a c -> p (a -> b) (c -> d) -> p b d
(<<**>>) = flip (<<*>>)

instance Biapplicative Pair where
  bipure a b = (a, b)
  (f, g) <<*>> (a, b) = (f a, g b)
