module Data.Verified.Biapplicative

import Data.Biapplicative
import Data.Verified.Bifunctor

class (VerifiedBifunctor p, Biapplicative p) =>
      VerifieBiapplicative (p : Type -> Type -> Type) where
  biapplicativeMap : (x : p a b) -> (f : a -> c) -> (g : b -> d) ->
                     bimap f g x = (bipure f g) <<*>> x
  biapplicativeIdentity : (x : p a b) -> (bipure id id) <<*>> x = x
  biapplicativeComposition : (x : p a b) -> (f1 : p (a -> c) (b -> d)) ->
                             (f2 : p (c -> e) (d -> f)) ->
                             (((bipure (.) (.)) <<*>> f2) <<*>> f1) <<*>> x =
                             f2 <<*>> (f1 <<*>> x)
  biapplicativeHomomorphism : (x : a) -> (y : b) -> (f1 : a -> c) ->
                              (f2 : b -> d) ->
                              (<<*>>) {p} (bipure f1 f2) (bipure x y) =
                              bipure {p} (f1 x) (f2 y)
  biapplicativeInterchange : (x : a) -> (y : b) -> (f : p (a -> c) (b -> d)) ->
                             f <<*>> (bipure x y) =
                             (bipure (\f'  : a -> c => f'  x)
                                     (\f'' : b -> d => f'' y)) <<*>> f

instance VerifieBiapplicative Pair where
  biapplicativeMap         (a, b)  f  g         = Refl
  biapplicativeIdentity    (a, b)               = Refl
  biapplicativeComposition (a, b) (f, g) (h, i) = Refl
  biapplicativeHomomorphism a  b   f  g         = Refl
  biapplicativeInterchange  a  b  (f, g)        = Refl
