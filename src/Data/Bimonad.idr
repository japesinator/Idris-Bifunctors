module Data.Bimonad

import Data.Biapplicative

||| Bimonads
||| @p the action of the first bifunctor component on pairs of objects
||| @q the action of the second bifunctor component on pairs of objects
class (Biapplicative p, Biapplicative q) =>
      Bimonad (p : Type -> Type -> Type) (q : Type -> Type -> Type) where

  ||| The equivalent of unit for standard monads
  biunit : a -> b -> (p a b, q a b)
  biunit a b = (bipure a b, bipure a b)

  ||| Like biunit, but returns only the first bifunctor
  bireturnl : a -> b -> p a b
  bireturnl a = fst . biunit a

  ||| Like biunit, but returns only the second bifunctor
  bireturnr : a -> b -> q a b
  bireturnr a = snd . biunit a

  ||| The equivalent of join for standard monads
  bijoin : (p (p a b) (q a b) -> p a b, q (p a b) (q a b) -> q a b)

  ||| Like bijoin, but only returns the first bifunctor
  bijoinl : p (p a b) (q a b) -> p a b
  bijoinl = fst bijoin

  ||| Like bijoin, but returns only the second bifunctor
  bijoinr : q (p a b) (q a b) -> q a b
  bijoinr = snd bijoin

  ||| Like the standard monadic bind operator
  bibind : p a b -> q a b -> (a -> p c d) -> (b -> q c d) -> (p c d, q c d)
  bibind pab qab p q = bijoin <<.>> ((bimap p q, bimap p q) <<.>> (pab, qab))

  ||| Like bibind but returns only the first bifunctor
  bibindl : p a b -> (a -> p c d) -> (b -> q c d) -> p c d
  bibindl pab p q = bijoinl (bimap p q pab)

  ||| Like bibind but returns only the second bifunctor
  bibindr : q a b -> (a -> p c d) -> (b -> q c d) -> q c d
  bibindr qab p q = bijoinr (bimap p q qab)
