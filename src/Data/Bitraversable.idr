module Data.Bitraversable

import Data.Bifunctor
import Data.Bifoldable
import Control.Monad.Identity

||| Bitraversables
||| @t A bifunctor and bifoldable object which can be traversed by monads
class (Bifunctor t, Bifoldable t) =>
      Bitraversable (t : Type -> Type -> Type) where

  ||| Evaluates functions on each element, building a new structure from results
  bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
  bitraverse f g = bisequence . bimap f g

  ||| Sequences all the actions, creating a new structure using the results
  bisequence : Applicative f => t (f a) (f b) -> f (t a b)
  bisequence = bitraverse id id

||| Leftwards state transformer
record StateL : Type -> Type -> Type where
  SL : (runStateL : s -> (s, a)) -> StateL s a

instance Functor (StateL s) where
  map f (SL k) = SL $ (\s => let (s', v) = k s in (s', f v))

instance Applicative (StateL s) where
  pure x = SL (\s => (s, x))
  (SL kf) <$> (SL kv) = SL $ (\s =>
                        let (s', f) = kf s
                            (s'', v') = kv s'
                        in (s'', f v'))

||| Traverses a structure leftwards with a state, creating a new structure
bimapAccumL : Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e)) ->
                                 a -> t b d -> (a, t c e)
bimapAccumL f g s t = runStateL (bitraverse (SL . flip f) (SL . flip g) t) s

||| Rightwards state transformer
record StateR : Type -> Type -> Type where
  SR : (runStateR : s -> (s, a)) -> StateR s a

instance Functor (StateR s) where
  map f (SR k) = SR $ (\s => let (s', v) = k s in (s', f v))

instance Applicative (StateR s) where
  pure x = SR (\s => (s, x))
  (SR kf) <$> (SR kv) = SR $ (\s =>
                        let (s', v) = kv s
                            (s'', f) = kf s'
                        in (s'', f v))

||| Traverses a structure rightwards with a state, creating a new structure
bimapAccumR : Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e)) ->
                                 a -> t b d -> (a, t c e)
bimapAccumR f g s t = runStateR (bitraverse (SR . flip f) (SR . flip g) t) s

instance Bitraversable Pair where
  bitraverse f g (a, b) = (map MkPair (f a)) <$> (g b)
