module Data.Bitraversable

import Data.Bifunctor
import Data.Bifoldable
import Control.Monad.Identity

%access public export

||| Bitraversables
||| @t A bifunctor and bifoldable object which can be traversed by monads
interface (Bifunctor t, Bifoldable t) =>
      Bitraversable (t : Type -> Type -> Type) where

  bitraverse : Applicative f => (a -> f c) -> (b -> f d) -> t a b -> f (t c d)
  bitraverse f g = bisequence . bimap f g

  ||| Sequences all the actions, creating a new structure using the results
  |||
  ||| ```idris example
  ||| bisequence (Just "hello", Just 42) == Just ("hello", 42)
  ||| ```
  |||
  bisequence : Applicative f => t (f a) (f b) -> f (t a b)
  bisequence = bitraverse id id

||| Evaluates functions on each element monadically, returning the results
|||
||| ```idris example
||| bimapM Just (Just . (+) 2) ("hello", 42) == Just ("hello", 44)
||| ```
|||
bimapM : (Monad m, Bitraversable t) => (a -> m c) ->
                                       (b -> m d) -> t a b -> m (t c d)
bimapM = bitraverse

||| Leftwards state transformer
record StateL s a where
  constructor SL
  runStateL : s -> (s, a)

implementation Functor (StateL s) where
  map f (SL k) = SL $ \s => let (s', v) = k s in (s', f v)

implementation Applicative (StateL s) where
  pure x = SL (\s => (s, x))
  (SL kf) <*> (SL kv) = SL $ \s => let (s', f) = kf s; (s'', v') = kv s'
                                   in (s'', f v')

||| bimapAccumL with the order of arguments reversed
biforAccumL : Bitraversable t => a -> t b d -> (a -> b -> (a, c)) ->
                                               (a -> d -> (a, e)) ->(a, t c e)
biforAccumL s t f g = runStateL (bitraverse (SL . flip f) (SL . flip g) t) s

||| Traverses a structure leftwards with a state, creating a new structure
bimapAccumL : Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e)) ->
                                 a -> t b d -> (a, t c e)
bimapAccumL f g s t = biforAccumL s t f g

||| Rightwards state transformer
record StateR s a where
  constructor SR
  runStateR : s -> (s, a)

implementation Functor (StateR s) where
  map f (SR k) = SR $ \s => let (s', v) = k s in (s', f v)

implementation Applicative (StateR s) where
  pure x = SR $ \s => (s, x)
  (SR kf) <*> (SR kv) = SR $ \s => let (s', v) = kv s; (s'', f) = kf s'
                                   in (s'', f v)

||| bimapAccuml with the order of arguments reversed
biforAccumR : Bitraversable t => a -> t b d -> (a -> b -> (a, c)) ->
                                               (a -> d -> (a, e)) ->(a, t c e)
biforAccumR s t f g = runStateR (bitraverse (SR . flip f) (SR . flip g) t) s

||| Traverses a structure rightwards with a state, creating a new structure
bimapAccumR : Bitraversable t => (a -> b -> (a, c)) -> (a -> d -> (a, e)) ->
                                 a -> t b d -> (a, t c e)
bimapAccumR f g s t = biforAccumR s t f g

implementation Bitraversable Pair where
  bitraverse f g (a, b) = map MkPair (f a) <*> (g b)

implementation Bitraversable Either where
  bitraverse f _ (Left a)  = map Left  $ f a
  bitraverse _ g (Right b) = map Right $ g b
