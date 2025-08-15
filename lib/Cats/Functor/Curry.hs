module Cats.Functor.Curry where

import Cats.Category
import Cats.Category.Exponential
import Cats.Category.Product
import Cats.Functor

-- Typing '₂': `^q 2 s`
type data Curry₂ :: forall a b c. ((a × b) --> c) -> NamesOf a -> (b --> c)

-- Typing '₁': `^q 1 s`
type data Curry₁ :: forall a b c. ((a × b) --> c) -> (a --> (c ^ b))

-- Typing '₀': `^q 0 s`
type data Curry₀ :: forall a b c. (c ^ (a × b)) --> ((c ^ b) ^ a)

type instance Act (Curry₂ f x) y = Act f '(x, y)

type instance Act (Curry₁ f) x = Curry₂ f x

type instance Act Curry₀ f = Curry₁ f

instance
  (Category a, Category b, Functor f, x ∈ a) =>
  Functor (Curry₂ @a @b f x)
  where
  map _ byz = map f (identity x :×: byz)

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry₁ @a @b @c f)
  where
  map _ axy = EXP \i ->
    map f (axy :×: identity i)

instance
  (Category a, Category b, Category c) =>
  Functor (Curry₀ @a @b @c)
  where
  map _ (EXP t) = EXP \i -> EXP \j -> t (i, j)
