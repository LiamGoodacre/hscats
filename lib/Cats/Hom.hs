module Cats.Hom where

import Cats.Category
import Cats.CrossProduct
import Cats.Curry
import Cats.Exponential
import Cats.Flip
import Cats.Functor
import Cats.Opposite

type data Hom :: forall c -> Op c × c --> Types

type instance Act (Hom c) o = c (Fst o) (Snd o)

instance (Category c) => Functor (Hom c) where
  map _ (OP f :×: g) t = g ∘ t ∘ f

-- Typing '⁰': `^q 0 S`
type Hom⁰ :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type Hom⁰ c = Curry₁ (Flip (Hom c))

-- Typing '₀': `^q 0 s`
type Hom₀ :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type Hom₀ c = Curry₁ (Hom c)
