module Cats.Exponential where

import Cats.Category
import Cats.Functor

data (^) :: forall c d -> CATEGORY (d --> c) where
  EXP ::
    { ($$) ::
        forall (i :: NamesOf d) ->
        (i ∈ d) =>
        c (Act f i) (Act g i)
    } ->
    (c ^ d) f g

type (~>) (f :: d --> c) g = (c ^ d) f g

type instance o ∈ (c ^ d) = Functor o

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = EXP \i -> (l $$ i) ∘ (r $$ i)

instance (Category d, Category c) => Category (c ^ d) where
  identity f = EXP \i -> identity (Act f i)
