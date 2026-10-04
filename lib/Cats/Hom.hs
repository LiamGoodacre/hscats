module Cats.Hom where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Cats.Opposite
import Cats.Profunctor

type data Hom :: forall c -> PROFUNCTOR c c

type instance Act (Hom c) o = c (Fst o) (Snd o)

instance (Category c) => Functor (Hom c) where
  map _ (OP f :×: g) t = g ∘ t ∘ f
