module Cats.Functor.Hom where

import Cats.Category
import Cats.Category.Exponential
import Cats.Category.Opposite
import Cats.Category.Product
import Cats.Functor
import Cats.Functor.Curry
import Cats.Functor.Spin

type data Hom :: forall c -> Op c × c --> Types

type instance Act (Hom c) o = c (Fst o) (Snd o)

instance (Category c) => Functor (Hom c) where
  map _ (OP f :×: g) t = g ∘ t ∘ f

-- Typing '⁰': `^q 0 S`
type Hom⁰ :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type Hom⁰ c = Curry¹ (Spin (Hom c))

-- Typing '₀': `^q 0 s`
type Hom₀ :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type Hom₀ c = Curry¹ (Hom c)
