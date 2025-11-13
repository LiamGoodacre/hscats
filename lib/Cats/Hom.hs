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

-- Typing '⁰': ` 0 S`
type Slice :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type Slice c = Curry₁ (Flip (Hom c))

-- Typing '¹': ` 1 S`
type Sliced :: forall (c :: CATEGORY o) -> NamesOf c -> Op c --> Types
type Sliced c = Curry₂ (Flip (Hom c))

-- Typing '₀': ` 0 s`
type Coslice :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type Coslice c = Curry₁ (Hom c)

-- Typing '₁': ` 1 s`
type Cosliced :: forall (c :: CATEGORY o) -> NamesOf (Op c) -> c --> Types
type Cosliced c = Curry₂ (Hom c)
