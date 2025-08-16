module Cats.Product where

import Cats.Category
import Data.Type.Equality (type (~))

data (×) :: CATEGORY s -> CATEGORY t -> CATEGORY (s, t) where
  (:×:) :: l a b -> r x y -> (l × r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type instance v ∈ (l × r) = (v ~ '(Fst v, Snd v), Fst v ∈ l, Snd v ∈ r)

instance (Semigroupoid l, Semigroupoid r) => Semigroupoid (l × r) where
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

instance (Category l, Category r) => Category (l × r) where
  identity (a, b) = identity a :×: identity b
