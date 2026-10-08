module Cats.Constructor where

import Cats.Category
import Cats.Compose
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Data.Kind (Type)
import Prelude qualified

type data Constructor (f :: Type -> Type) :: Types --> Types

type instance Act (Constructor f) a = f a

instance (Prelude.Functor f) => Functor (Constructor f) where
  map _ = Prelude.fmap

-- | The ordinary Haskell monad operations form a monoid under composition.
-- The instance belongs to the constructor tag, so it needs no orphan or
-- blanket instance for arbitrary functors.
instance (Prelude.Monad f) => MonoidObject Composing (Constructor f) where
  empty _ _ = EXP \_ -> Prelude.pure
  append _ _ = EXP \_ mm -> mm Prelude.>>= Prelude.id
