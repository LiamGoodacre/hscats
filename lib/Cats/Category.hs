-- | Categories with an explicit kind of object names and an object predicate.
-- 'Obj' describes valid names; '(∈)' carries that evidence into operations
-- such as 'identity'. Arrows are represented by an indexed Haskell type.
module Cats.Category where

import Cats.Core
import Cats.Semigroupoid
import Data.Kind (Constraint)

-- | A semigroupoid with identities. For @f :: k a b@ between valid objects,
-- @identity b ∘ f = f@ and @f ∘ identity a = f@. The object constraints
-- provide evidence needed to construct identities; they do not prove the laws.
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o
