module Cats.Category.Opposite where

import Cats.Category

{- Category: opposites -}

data Op :: CATEGORY i -> CATEGORY i where
  OP :: {runOP :: k b a} -> Op k a b

type instance i ∈ Op k = i ∈ k

instance (Semigroupoid k) => Semigroupoid (Op k) where
  OP g ∘ OP f = OP (f ∘ g)

instance (Category k) => Category (Op k) where
  identity o = OP (identity o)
