module Data.Verified.Biapplicative

import Data.Biapplicative
import Data.Bifunctor
import Data.Verified.Bifunctor

%access public export

||| Verified Biapplicatives
||| A Biapplicative for which all the Applicative laws hold
class (VerifiedBifunctor p, Biapplicative p) =>
      VerifiedBiapplicative (p : Type -> Type -> Type) where
  biapplicativeMap           : (x : p a b) -> (f : a -> c) -> (g : b -> d) ->
                               bimap f g x = (bipure f g) <<*>> x
  biapplicativeIdentity      : (x : p a b) -> (bipure id id) <<*>> x = x
  biapplicativeComposition   : (x : p a b) -> (f : p (a -> c) (b -> d)) ->
                               (g : p (c -> e) (d -> a')) ->
                               (((bipure (.) (.)) <<*>> g) <<*>> f) <<*>> x =
                               g <<*>> (f <<*>> x)
  biapplicativeHomomorphism  : (x : a) -> (y : b) -> (f : a -> c) ->
                               (g : b -> d) ->
                               (<<*>>) {p} (bipure f g) (bipure x y) =
                               bipure {p} (f x) (g y)
  biapplicativeInterchange   : (x : a) -> (y : b) ->
                               (f : p (a -> c) (b -> d)) ->
                               f <<*>> (bipure x y) =
                               (bipure (\f'  : a -> c => f'  x)
                                       (\f'' : b -> d => f'' y)) <<*>> f

instance VerifiedBiapplicative Pair where
  biapplicativeMap         (_, _)  _  _         = Refl
  biapplicativeIdentity    (_, _)               = Refl
  biapplicativeComposition (_, _) (_, _) (_, _) = Refl
  biapplicativeHomomorphism _  _   _  _         = Refl
  biapplicativeInterchange  _  _  (_, _)        = Refl
