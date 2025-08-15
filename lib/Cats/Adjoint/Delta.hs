module Cats.Adjoint.Delta where

import Cats.Adjoint
import Cats.Category
import Cats.Category.Exponential
import Cats.Category.Product
import Cats.Functor
import Prelude qualified

-- (∨) ⊣ Δ₂ Types ⊣ (∧)

type data Δ₂ :: forall (k :: CATEGORY i) -> (k --> (k × k))

type instance Act (Δ₂ k) x = '(x, x)

instance (Category k) => Functor (Δ₂ k) where
  map _ f = f :×: f

type data (∧) :: (Types × Types) --> Types

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map _ (f :×: g) (a, b) = (f a, g b)

type data (∨) :: (Types × Types) --> Types

type instance Act (∨) x = Prelude.Either (Fst x) (Snd x)

instance Functor (∨) where
  map _ (f :×: g) = Prelude.either (Prelude.Left ∘ f) (Prelude.Right ∘ g)

instance Δ₂ Types ⊣ (∧) where
  leftAdjoint _ _ t = (Prelude.fst ∘ t) :×: (Prelude.snd ∘ t)
  rightAdjoint _ _ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ₂ Types where
  leftAdjoint _ _ (f :×: g) = f `Prelude.either` g
  rightAdjoint _ _ t = (t ∘ Prelude.Left) :×: (t ∘ Prelude.Right)

-- (∃) ⊣ Δ @Types ⊣ (∀)

type data Δ' :: NamesOf k -> x --> k

type instance Act (Δ' a) b = a

instance (Category k, Category x, a ∈ k) => Functor (Δ' @k @x a) where
  map _ _ = identity _

type data Δ :: k --> (k ^ x)

type instance Act (Δ @k) a = Δ' @k a

instance (Category k, Category x) => Functor (Δ @k @x) where
  map _ ab = EXP \_ -> ab

type data Exists :: forall d c. (c ^ d) --> c

data family DataExists (f :: d --> c)

data instance DataExists (f :: d --> Types) where
  DataExistsTypes :: forall {d} i (f :: d --> Types). (i ∈ d) => Act f i -> DataExists f

type instance Act (Exists @d @Types) f = DataExists f

instance (Category d) => Functor (Exists @d @Types) where
  map _ (t :: f ~> g) (DataExistsTypes @i (fi :: Act f i)) = DataExistsTypes @i ((t $$ i) fi)

type data Forall :: forall d c. (c ^ d) --> Types

data family DataForall (f :: d --> c)

type instance Act (Forall @d @c) f = DataForall f

data instance DataForall (f :: d --> Types) where
  DataForallTypes :: forall {d} (f :: d --> Types). {runForallTypes :: forall i -> (i ∈ d) => Act f i} -> DataForall f

instance (Category d) => Functor (Forall @d @Types) where
  map _ t (DataForallTypes ifi) = DataForallTypes \i -> (t $$ i) (ifi i)

instance Δ @Types ⊣ Forall @Types where
  leftAdjoint _ _ ab = EXP \i a -> runForallTypes (ab a) i
  rightAdjoint _ _ ab a = DataForallTypes \i -> (ab $$ i) a
