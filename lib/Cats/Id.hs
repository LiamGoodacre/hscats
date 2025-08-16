module Cats.Id where

import Cats.Category
import Cats.Functor

type data Id :: forall k. k --> k

type instance Act Id x = x

type instance Super Functor Id = ()

instance (Category k) => Functor (Id :: k --> k) where
  map _ f = f
