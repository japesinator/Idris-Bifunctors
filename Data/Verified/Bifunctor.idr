module Data.Verified.Bifunctor

import Data.Bifunctor

||| Verified Bifunctors
||| A Bifunctor for which identity and composition laws are verified
public export
interface Bifunctor p => VerifiedBifunctor (0 p : Type -> Type -> Type) where
  bifunctorIdentity : (x : p a b) -> bimap Basics.id Basics.id x = x
  bifunctorComposition : (x : p a d) -> (f : a -> b) -> (g : b -> c) ->
                         (h : d -> e) -> (i : e -> a') ->
                         (bimap (g . f) (i . h) x) =
                         (bimap g i . bimap f h) x

public export
implementation VerifiedBifunctor Either where
  bifunctorIdentity    (Left  _)         = Refl
  bifunctorIdentity    (Right _)         = Refl
  bifunctorComposition (Left  _) _ _ _ _ = Refl
  bifunctorComposition (Right _) _ _ _ _ = Refl

public export
implementation VerifiedBifunctor Pair where
  bifunctorIdentity    (_, _)         = Refl
  bifunctorComposition (_, _) _ _ _ _ = Refl
