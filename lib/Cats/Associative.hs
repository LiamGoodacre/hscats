module Cats.Associative where

import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

-- | An associative tensor, with mutually inverse, natural associators.
-- In tensor notation, write @a ⊗ b = Act op '(a, b)@, tensor arrows using
-- @map op@, and write @alpha(a,b,c) = rassoc op a b c@. Then 'lassoc'
-- is the inverse of @alpha@, in both directions. Naturality requires:
--
-- @
-- alpha(a',b',c') ∘ ((f ⊗ g) ⊗ h)
--   = (f ⊗ (g ⊗ h)) ∘ alpha(a,b,c)
-- @
--
-- The pentagon law equates the two reassociations from
-- @((a ⊗ b) ⊗ c) ⊗ d@ to @a ⊗ (b ⊗ (c ⊗ d))@:
--
-- @
-- alpha(a,b,c ⊗ d) ∘ alpha(a ⊗ b,c,d)
--   = (id_a ⊗ alpha(b,c,d)) ∘ alpha(a,b ⊗ c,d)
--       ∘ (alpha(a,b,c) ⊗ id_d)
-- @
--
-- These equations apply to valid objects and arrows. 'Functor' supplies
-- structural evidence; instance authors must establish the coherence laws.
type Associative ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  Constraint
class (Functor op) => Associative (op :: BINARY_OP k) where
  lassoc ::
    forall op' a b c ->
    (op' ~ op) =>
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      ((a ☼ (b ☼ c) op) op)
      (((a ☼ b) op ☼ c) op)
  rassoc ::
    forall op' a b c ->
    (op' ~ op) =>
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      (((a ☼ b) op ☼ c) op)
      ((a ☼ (b ☼ c) op) op)
