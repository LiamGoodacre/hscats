module Cats.Monoidal where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Data.Kind (Constraint)

type MonoidalEmpty :: BINARY_OP k -> NamesOf k
type family MonoidalEmpty p

-- | An associative tensor with unit object @i = MonoidalEmpty p@.
-- Write @lambda_a = idl@ and @rho_a = idr@; 'coidl' and 'coidr' must be their
-- inverses in both directions. In the tensor notation of "Cats.Associative",
-- the unitors are natural: for @h : a -> b@,
--
-- @
-- h ∘ lambda_a = lambda_b ∘ (id_i ⊗ h)
-- h ∘ rho_a = rho_b ∘ (h ⊗ id_i)
-- @
--
-- In addition to the associator's pentagon law, the triangle must commute:
--
-- @
-- rho_a ⊗ id_b = (id_a ⊗ lambda_b) ∘ alpha(a,i,b)
-- @
--
-- Both sides map @(a ⊗ i) ⊗ b@ to @a ⊗ b@. At the unit object,
-- @lambda_i = rho_i@. These are laws of instances, not proofs carried by
-- the superclass constraints.
type Monoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class
  (Associative p, MonoidalEmpty p ∈ k) =>
  Monoidal (p :: BINARY_OP k)
  where
  idl :: (m ∈ k) => k ((MonoidalEmpty p ☼ m) p) m
  coidl :: (m ∈ k) => k m ((MonoidalEmpty p ☼ m) p)
  idr :: (m ∈ k) => k ((m ☼ MonoidalEmpty p) p) m
  coidr :: (m ∈ k) => k m ((m ☼ MonoidalEmpty p) p)
