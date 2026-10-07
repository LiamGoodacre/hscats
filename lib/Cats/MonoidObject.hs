module Cats.MonoidObject where

import Cats.Binary
import Cats.Category
import Cats.Monoidal
import Cats.Opposite
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

-- | A monoid for a monoidal tensor. For @u = empty p m@ and
-- @mu = append p m@, lawful instances satisfy:
--
-- @
-- mu ∘ map p (mu :×: identity m)
--   = mu ∘ map p (identity m :×: mu) ∘ rassoc p m m m
-- mu ∘ map p (u :×: identity m) = idl
-- mu ∘ map p (identity m :×: u) = idr
-- @
--
-- These are equations between arrows in the underlying category. If those
-- arrows are natural transformations, they must also satisfy naturality.
-- The superclasses provide monoidal and object evidence, not proofs of laws.
type MonoidObject ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  Constraint
class
  ( Monoidal p,
    m ∈ k
  ) =>
  MonoidObject (p :: BINARY_OP k) m
  where
  empty ::
    forall q n ->
    (p ~ q, m ~ n) =>
    k (MonoidalEmpty p) m
  append ::
    forall q n ->
    (p ~ q, m ~ n) =>
    k ((m ☼ m) p) m

-- | A comonoid is a monoid for the opposite tensor. Define its instance as
-- MonoidObject (OpTensor p) m; the operations below unwrap the reversed arrows.
-- Comultiplication must be coassociative up to the associator, and applying
-- the counit to either output must give the identity up to the unitors.
type ComonoidObject :: BINARY_OP k -> NamesOf k -> Constraint
type ComonoidObject p m = (Monoidal p, MonoidObject (OpTensor p) m)

-- | The comonoid counit (discard).
coempty ::
  forall {k}.
  forall (p :: BINARY_OP k) m ->
  (ComonoidObject p m) =>
  k m (MonoidalEmpty p)
coempty p m = runOP (empty (OpTensor p) m)

-- | The comonoid comultiplication.
coappend ::
  forall {k}.
  forall (p :: BINARY_OP k) m ->
  (ComonoidObject p m) =>
  k m ((m ☼ m) p)
coappend p m = runOP (append (OpTensor p) m)
