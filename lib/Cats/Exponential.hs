module Cats.Exponential where

import Cats.Category
import Cats.Functor

-- | The functor category, with natural transformations as arrows.
--
-- For functors @f@ and @g@, a component family @t :: f ~> g@ must satisfy
-- naturality for every @h :: d a b@ between valid objects:
--
-- @
-- map g h ∘ (t $$ a) = (t $$ b) ∘ map f h
-- @
--
-- 'EXP' only stores the component family; its type does not enforce this law
-- or carry 'Functor' evidence for its endpoints. For example, in a one-object
-- category with integer arrows composed by addition, a functor can map arrow
-- @n@ to addition by @n@ on integers. Doubling is a well-typed component of an
-- endotransformation but is not natural: adding one after doubling differs
-- from doubling after adding one.
--
-- Consumers must supply lawful transformations. In particular, horizontal
-- composition in "Cats.Compose" relies on naturality to preserve composition.
-- The 'Obj' constraint below supplies functor evidence when a construction
-- requires valid objects of this category; constructing 'EXP' alone does not.
data (^) :: forall c d -> CATEGORY (d --> c) where
  EXP ::
    { ($$) ::
        forall (i :: NamesOf d) ->
        (i ∈ d) =>
        c (Act f i) (Act g i)
    } ->
    (c ^ d) f g

type (~>) (f :: d --> c) g = (c ^ d) f g

type instance Obj (c ^ d) o = Functor o

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = EXP \(type i) -> (l $$ i) ∘ (r $$ i)

instance (Category d, Category c) => Category (c ^ d) where
  identity f = EXP \(type i) -> identity (Act f i)
