module Cats.Constructor where

import Cats.Category
import Cats.Functor
import Data.Kind (Type)
import Prelude qualified

type data Constructor (f :: Type -> Type) :: Types --> Types

type instance Act (Constructor f) a = f a

type instance Super Functor (Constructor f) = ()

instance (Prelude.Functor f) => Functor (Constructor f) where
  map _ = Prelude.fmap
