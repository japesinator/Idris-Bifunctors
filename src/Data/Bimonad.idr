module Data.Bimonad

import Data.Bifunctor
import Data.Biapplicative

%access public export

infixl 4 >>==

||| Bimonads
||| @p the action of the first Bifunctor component on pairs of objects
||| @q the action of the second Bifunctor component on pairs of objects
interface (Biapplicative p, Biapplicative q) =>
      Bimonad (p : Type -> Type -> Type) (q : Type -> Type -> Type) where

  ||| The equivalent of `join` for standard Monads
  |||
  ||| ````idris example
  ||| bijoin (((1, "hello"      ), (2, "goodbye"      )),
  |||         ((3, "hello again"), (4, "goodbye again"))) ==
  ||| ((1, "hello"), (3, "goodbye again"))
  ||| ````
  |||
  bijoin : (p (p a b) (q a b), q (p a b) (q a b)) -> (p a b, q a b)
  bijoin p = p >>== (id, id)

  ||| Like the standard monadic bind operator
  |||
  ||| ````idris example
  ||| ((1, "hello"), (2, "goodbye")) >>== ((\x => (x, "hi")), (\x => (3, x))) ==
  ||| ((1, "hi"), (3, "goodbye"))
  ||| ````
  |||
  (>>==) : (p a b, q a b) -> ((a -> p c d), (b -> q c d)) -> (p c d, q c d)
  (pab, qab) >>== (f, g) = bijoin $ (bimap f g, bimap f g) <<*>> (pab, qab)

||| The equivalent of `unit` for standard Monads
|||
||| ````idris example
||| biunit 1 "hello" == ((1, "hello"), (1, "hello"))
||| ````
|||
biunit : Bimonad p q => a -> b -> (p a b, q a b)
biunit a b = (bipure a b, bipure a b)

implementation Bimonad Pair Pair where
  bijoin = bimap fst snd
