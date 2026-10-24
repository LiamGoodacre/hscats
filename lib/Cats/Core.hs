module Cats.Core where

import Data.Kind (Constraint, Type)

infix 4 ∈

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

-- | Bring evidence into a local scope, often after instantiating a quantified
-- superclass such as @Acts f a@.
require :: (c) => ((c) => r) -> r
require r = r

-- | Turn an 'Obj' predicate into the '(∈)' evidence used by the public API.
member ::
  forall (k :: CATEGORY i) (o :: i) ->
  (Obj k o) =>
  ((o ∈ k) => r) -> r
member _ _ result = result
