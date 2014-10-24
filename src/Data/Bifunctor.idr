module Data.Bifunctor

class Bifunctor (p : Type -> Type -> Type) where
  bimap : (a -> b) -> (c -> d) -> p a c -> p b d
  bimap f g = first f . second g

  first : (a -> b) -> p a c -> p b c
  first f = bimap f id

  second : (a -> b) -> p c a -> p c b
  second = bimap id

instance Bifunctor Either where
  bimap f _ (Left a) = Left (f a)
  bimap _ g (Right b) = Right (g b)
