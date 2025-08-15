module Cats.Adjoint.Δ where

import Cats.Adjoint
import Cats.Category
import Cats.Category.Product
import Cats.Functor
import Prelude qualified

-- (∨) ⊣ Δ₂ Types ⊣ (∧)

data Δ₂ :: forall (k :: CATEGORY i) -> (k --> (k × k))

type instance Act (Δ₂ k) x = '(x, x)

instance (Category k) => Functor (Δ₂ k) where
  map _ f = f :×: f

data (∧) :: (Types × Types) --> Types

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map _ (f :×: g) (a, b) = (f a, g b)

data (∨) :: (Types × Types) --> Types

type instance Act (∨) x = Prelude.Either (Fst x) (Snd x)

instance Functor (∨) where
  map _ (f :×: g) = Prelude.either (Prelude.Left ∘ f) (Prelude.Right ∘ g)

instance Δ₂ Types ⊣ (∧) where
  leftAdjoint _ _ t = (Prelude.fst ∘ t) :×: (Prelude.snd ∘ t)
  rightAdjoint _ _ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ₂ Types where
  leftAdjoint _ _ (f :×: g) = f `Prelude.either` g
  rightAdjoint _ _ t = (t ∘ Prelude.Left) :×: (t ∘ Prelude.Right)
