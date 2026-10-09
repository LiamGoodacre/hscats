-- | Representable functors and their embeddings into functor categories.
-- 'HomTo' fixes a target and varies the source contravariantly; 'HomFrom'
-- fixes a source and varies the target covariantly. The embeddings vary the
-- fixed endpoint and return natural transformations between representables.
--
-- These are hom-valued functors, not slice or coslice categories. The latter
-- have arrows into or out of a fixed object as their objects, with commuting
-- triangles as morphisms. The present aliases are defined by currying 'Hom'.
module Cats.Yoneda where

import Cats.Category
import Cats.Curry
import Cats.Exponential
import Cats.Flip
import Cats.Functor
import Cats.Hom
import Cats.Opposite

-- | The embedding @c -> (Types ^ Op c)@ taking @a@ to @HomTo c a@.
-- An arrow @f :: c a b@ induces the natural transformation with component
-- @h -> f ∘ h@ at each source object. Use @map (YonedaEmbedding c) f $$ x@
-- to select that component.
type YonedaEmbedding :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type YonedaEmbedding c = Curry₁ (Flip (Hom c))

-- | Arrows into a fixed target: @Act (HomTo c a) x = c x a@.
-- Mapping @OP f@ precomposes each arrow with @f@. The functor instance
-- requires @Category c@ and evidence that @a@ is a valid object.
type HomTo :: forall (c :: CATEGORY o) -> NamesOf c -> Op c --> Types
type HomTo c = Curry₂ (Flip (Hom c))

-- | The embedding @Op c -> (Types ^ c)@ taking @a@ to @HomFrom c a@.
-- An arrow @OP f@, where @f :: c b a@, induces components @h -> h ∘ f@.
type CoyonedaEmbedding :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type CoyonedaEmbedding c = Curry₁ (Hom c)

-- | Arrows out of a fixed source: @Act (HomFrom c a) x = c a x@.
-- Mapping @f@ postcomposes each arrow with @f@. The functor instance requires
-- @Category c@ and evidence that @a@ is a valid object.
type HomFrom :: forall (c :: CATEGORY o) -> NamesOf (Op c) -> c --> Types
type HomFrom c = Curry₂ (Hom c)
