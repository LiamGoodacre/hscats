module Cats.Functor.Id where

import Cats.Category
import Cats.Functor

data Id :: forall k. k --> k

type instance Act Id x = x

instance (Category k) => Functor (Id :: k --> k) where
  map _ f = f
