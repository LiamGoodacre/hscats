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
type family Obj (k :: CATEGORY i) (x :: i) :: Constraint

-- Class arguments retain the object and category for inference; the superclass
-- exposes the category-specific object constraint.
class (Obj k x) => (x :: i) ∈ (k :: CATEGORY i)

instance (Obj k x) => x ∈ k

-- Semigroupoids have a means of composing arrows
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: k a b -> k x a -> k x b

-- Categories are Semigroupoids with an identity arrow
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o

-- "Equality" forms a category
type instance Obj (:~:) t = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl

-- "Type" forms a category
type Types = (->) :: CATEGORY Type

type instance Obj Types t = (t ~ t)

instance Semigroupoid Types where
  (f ∘ g) x = f (g x)

instance Category Types where
  identity _ x = x

with :: (c) => ((c) => r) -> r
with r = r

member ::
  forall (k :: CATEGORY i) (o :: i) ->
  (Obj k o) =>
  ((o ∈ k) => r) -> r
member _ _ result = result
