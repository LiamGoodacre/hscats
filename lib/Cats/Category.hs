-- | Categories with an explicit kind of object names and an object predicate.
-- 'Obj' describes valid names; '(∈)' carries that evidence into operations
-- such as 'identity'. Arrows are represented by an indexed Haskell type.
module Cats.Category where

import Data.Kind (Constraint, Type)
import Data.Type.Equality ((:~:) (Refl), type (~))

infix 4 ∈
infixr 9 ∘

-- | A category's arrow type, indexed by source and target object names.
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- | The kind of object names used by a category.
type NamesOf :: forall i. CATEGORY i -> Type
type NamesOf @i c = i

-- | Predicate defining which names denote valid objects in a category.
type family Obj (k :: CATEGORY i) (x :: i) :: Constraint

-- | Class arguments retain the object and category for inference; the superclass
-- exposes the category-specific object constraint.
class (Obj k x) => (x :: i) ∈ (k :: CATEGORY i)

instance (Obj k x) => x ∈ k

-- | Composition must be associative: @(h ∘ g) ∘ f = h ∘ (g ∘ f)@.
-- These equations compare parallel arrows between valid objects.
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: k a b -> k x a -> k x b

-- | A semigroupoid with identities. For @f :: k a b@ between valid objects,
-- @identity b ∘ f = f@ and @f ∘ identity a = f@. The object constraints
-- provide evidence needed to construct identities; they do not prove the laws.
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o

-- "Equality" forms a category
type instance Obj (:~:) t = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl

-- | Haskell types as objects and functions as arrows.
type Types = (->) :: CATEGORY Type

type instance Obj Types t = (t ~ t)

instance Semigroupoid Types where
  (f ∘ g) x = f (g x)

instance Category Types where
  identity _ x = x

-- | Bring evidence into a local scope, often after instantiating a quantified
-- superclass such as @Acts f a@.
with :: (c) => ((c) => r) -> r
with r = r

-- | Turn an 'Obj' predicate into the '(∈)' evidence used by the public API.
member ::
  forall (k :: CATEGORY i) (o :: i) ->
  (Obj k o) =>
  ((o ∈ k) => r) -> r
member _ _ result = result
