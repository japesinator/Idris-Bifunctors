module Data.Bifunctor.Apply

import Data.Bifunctor

infixl 4 <<$>>, <<.>>, <<., .>>, <<..>>

||| Primarily used to make the definitions of bilift2 and bilift3 pretty
(<<$>>) : (a -> b) -> a -> b
(<<$>>) = id

class Bifunctor p => Biapply (p : Type -> Type -> Type) where

  ||| Applys a bifunctor of functions to another bifunctor of the same type
  (<<.>>) : p (a -> b) (c -> d) -> p a c -> p b d

  ||| Given two bifunctors, returns the left
  (<<.) : p a b -> p c d -> p a b
  a <<. b = bimap const const <<$>> a <<.>> b

  ||| Given two bifunctors, returns the right
  (.>>) : p a b -> p c d -> p c d
  a .>> b = bimap (const id) (const id) <<$>> a <<.>> b

||| Lifts a binary function into a bifunctor
bilift2 : Biapply w => (a -> b -> c) -> (d -> e -> f) -> w a d -> w b e -> w c f
bilift2 f g a b = bimap f g <<$>> a <<.>> b

||| Lifts a ternary function into a bifunctor
bilift3 : Biapply w => (a -> b -> c -> d) -> (e -> f -> g -> h) -> w a e -> w b f -> w c g -> w d h
bilift3 f g a b c = bimap f g <<$>> a <<.>> b <<.>> c

||| Applies the second of two bifunctors of the same type to the first
(<<..>>): Biapply p => p a c -> p (a -> b) (c -> d) -> p b d
(<<..>>) = flip (<<.>>)
