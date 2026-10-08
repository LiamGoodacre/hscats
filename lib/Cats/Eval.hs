-- | Evaluate a functor at an object, functorially in both arguments.
-- Arrows in the functor category must be natural transformations: the type
-- of 'EXP' alone does not guarantee this (see "Cats.Exponential").
module Cats.Eval (Eval) where

import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor

-- | @Act Eval '(f, x) = Act f x@. On a pair consisting of a natural
-- transformation @t :: f ~> g@ and an arrow @h :: d x y@, evaluation gives
-- @map g h ∘ (t $$ x)@. Naturality makes this equal to
-- @(t $$ y) ∘ map f h@ and ensures preservation of composition.
type data Eval :: forall d c. ((c ^ d) × d) --> c

type instance Act Eval fx = Act (Fst fx) (Snd fx)

instance (Category d, Category c) => Functor (Eval @d @c) where
  map @a @b _ (f :×: x) =
    with @(Fst b ∈ (c ^ d)) do
      map (Fst b) x ∘ (f $$ Snd a)
