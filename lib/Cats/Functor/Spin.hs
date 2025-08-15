module Cats.Functor.Spin where

import Cats.Category
import Cats.Category.Product
import Cats.Functor

{- Spin -}

data Spin :: ((d × c) --> k) -> ((c × d) --> k)

type instance Act (Spin b) x = Act b '(Snd x, Fst x)

instance
  (Category d, Category c, Functor b) =>
  Functor (Spin (b :: (d × c) --> k))
  where
  map _ (l :×: r) = map b (r :×: l)
