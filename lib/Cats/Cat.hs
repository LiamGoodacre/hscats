module Cats.Cat where

import Cats.Category
import Cats.Compose
import Cats.Functor
import Cats.Id
import Data.Proxy (Proxy (Proxy))

data Cat :: forall k. CATEGORY (CATEGORY k) where
  CAT :: (Functor (f :: a --> b)) => Proxy f -> Cat a b

type instance c ∈ Cat = Category c

instance Semigroupoid Cat where
  CAT (Proxy @f) ∘ CAT (Proxy @g) =
    CAT (Proxy @(f • g))

instance Category Cat where
  identity _ = CAT (Proxy @Id)
