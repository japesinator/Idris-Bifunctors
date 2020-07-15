module Data.Bifunctor.Tannen

import Data.Bifunctor
import Data.Bifunctor.Apply
import Data.Biapplicative
import Data.Bifoldable
import Data.Bitraversable
import Data.Morphisms

||| Compose a Bifunctor inside a Functor
|||
||| ````idris example
||| Tannen (Just (1, "hello"))
||| ````
|||
public export
record Tanned (f : Type -> Type) (p : Type -> Type -> Type) a b where
  constructor Tannen
  runTannen : f (p a b)

public export
implementation (Bifunctor p, Functor f) => Bifunctor (Tanned f p) where
  bimap f g = Tannen . map (bimap f g) . runTannen

public export
implementation (Bifunctor p, Functor f) => Functor (Tanned f p a) where
  map f = Tannen . map (second f) . runTannen

public export
implementation (Biapplicative p, Applicative f) => Biapplicative (Tanned f p) where
  bipure a b = Tannen . pure $ bipure a b
  (Tannen fg) <<*>> (Tannen xy) = Tannen $ (map (<<*>>) fg) <*> xy

public export
implementation (Foldable f, Bifoldable p) => Bifoldable (Tanned f p) where
  bifoldMap f g = (foldr ((<+>) . (bifoldMap f g)) neutral) . runTannen

public export
implementation (Foldable f, Bifoldable p) => Foldable (Tanned f p a) where
  foldr f z t = applyEndo ((((concatMap . bifoldMap (const neutral)
                                                  $ Endo . f)) . runTannen) t) z

public export
implementation (Traversable f, Bitraversable p) => Bitraversable (Tanned f p) where
  bitraverse f g = map Tannen . traverse (bitraverse f g) . runTannen

public export
implementation (Traversable f, Bitraversable p) => Traversable (Tanned f p a) where
  traverse f = map Tannen . traverse (bitraverse pure f) . runTannen
