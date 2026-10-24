module Cats.Semigroupoid where

import Cats.Core
import Data.Kind (Constraint)

infixr 9 ∘

-- | Composition must be associative: @(h ∘ g) ∘ f = h ∘ (g ∘ f)@.
-- These equations compare parallel arrows between valid objects.
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: k a b -> k x a -> k x b
