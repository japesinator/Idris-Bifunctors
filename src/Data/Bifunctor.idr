module Data.Bifunctor

||| Bifunctors
||| @p The action of the bifunctor on objects
class Bifunctor (p : Type -> Type -> Type) where
  ||| The action of the bifunctor on pairs of morphisms
  ||| @p the bifunctor
  ||| @m the morphism on the first component
  ||| @n the morphism on the second component
  bimap : (m : a -> b) -> (n : c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  ||| The action of the bifunctor on morphisms pertaining to the first object
  ||| @p the bifunctor
  ||| @m the morphism on the first component
  first : (m : a -> b) -> p a c -> p b c
  first f = bimap f id

  ||| The action of the bifunctor on morphisms pertaining to the second object
  ||| @p the bifunctor
  ||| @m the morphism on the first component
  second : (m : a -> b) -> p c a -> p c b
  second = bimap id

instance Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)

instance Bifunctor Pair where
  bimap f g (a, b) = (f a, g b)
