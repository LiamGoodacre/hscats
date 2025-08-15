module Cats.Functor.Curry where

import Cats.Category
import Cats.Category.Exponential
import Cats.Category.Product
import Cats.Functor

{- Functor: eval/curry -}

-- Typing '²': `^q 2 S`
data Curry² :: forall a b c. ((a × b) --> c) -> NamesOf a -> (b --> c)

-- Typing '¹': `^q 1 S`
data Curry¹ :: forall a b c. ((a × b) --> c) -> (a --> (c ^ b))

-- Typing '⁰': `^q 0 S`
data Curry⁰ :: forall a b c. (c ^ (a × b)) --> ((c ^ b) ^ a)

type instance Act (Curry² f x) y = Act f '(x, y)

type instance Act (Curry¹ f) x = Curry² f x

type instance Act Curry⁰ f = Curry¹ f

instance
  (Category a, Category b, Functor f, x ∈ a) =>
  Functor (Curry² @a @b f x)
  where
  map _ byz = map f (identity x :×: byz)

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry¹ @a @b @c f)
  where
  map _ axy = EXP \i ->
    map f (axy :×: identity i)

instance
  (Category a, Category b, Category c) =>
  Functor (Curry⁰ @a @b @c)
  where
  map _ (EXP t) = EXP \i -> EXP \j -> t (i, j)
