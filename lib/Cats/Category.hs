module Cats.Category where

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (Refl), type (~))

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Lookup the type of a category's object names
type NamesOf :: forall i. CATEGORY i -> Type
type NamesOf @i c = i

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k

-- Semigroupoids have a means of composing arrows
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- Categories are Semigroupoids with an identity arrow
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o

-- "Equality" forms a category
type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl

-- "Type" forms a category
type Types = (->) :: CATEGORY Type

type instance t ∈ Types = (t ~ t)

instance Semigroupoid Types where
  (f ∘ g) x = f (g x)

instance Category Types where
  identity _ x = x
