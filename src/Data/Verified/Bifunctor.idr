module Data.Verified.Bifunctor
import Data.Bifunctor

||| Verified Bifunctors
||| A bifunctor for which identity and composition laws are verified
class Bifunctor p => VerifiedBifunctor (p : Type -> Type -> Type) where
  bifunctorIdentity : {a : Type} -> {b : Type} -> (x : p a b) ->
                      bimap id id x = x
  bifunctorComposition : {a : Type} -> {b : Type} -> {c : Type} ->
                         {d : Type} -> {e : Type} -> {a' : Type} ->
                         (x : p a d) -> (f : a -> b) -> (g : b -> c) ->
                         (h : d -> e) -> (i : e -> a') ->
                         (bimap (g . f) (i . h) x) =
                         (bimap g i . bimap f h) x

instance VerifiedBifunctor Either where
  bifunctorIdentity    (Left _ )         = Refl
  bifunctorIdentity    (Right _)         = Refl
  bifunctorComposition (Left _ ) f g h i = Refl
  bifunctorComposition (Right _) f g h i = Refl

instance VerifiedBifunctor Pair where
  bifunctorIdentity    (a, b)         = Refl
  bifunctorComposition (a, b) f g h i = Refl
