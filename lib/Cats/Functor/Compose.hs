module Cats.Functor.Compose where

import Cats.Category
import Cats.Functor

data (•) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f • g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f • g) where
  map _ = map f ∘ map g
