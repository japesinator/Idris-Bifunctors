module Data.Profunctor

||| Profunctors
||| @p The action of the profunctor on pairs of objects
class Profunctor (p : Type -> Type -> Type) where
  ||| The action of the profunctor on pairs of morphisms
  dimap : (a -> b) -> (c -> d) -> p b c -> p a d
  dimap f g = lmap f . rmap g

  ||| The action of the profunctor on the contravariant morphism
  lmap : (a -> b) -> p b c -> p a c
  lmap f = dimap f id

  ||| The action of the profunctor on the covariant morphism
  rmap : (a -> b) -> p c a -> p c b
  rmap = dimap id
