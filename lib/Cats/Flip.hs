module Cats.Flip where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor

type data Flip :: ((d × c) --> k) -> ((c × d) --> k)

type instance Act (Flip b) x = Act b '(Snd x, Fst x)

instance
  (Category d, Category c, Functor b) =>
  Functor (Flip (b :: (d × c) --> k))
  where
  map _ (l :×: r) = map b (r :×: l)
