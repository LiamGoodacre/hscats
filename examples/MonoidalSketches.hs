-- | Compile-checked proposals for braided, symmetric, and closed structure.
-- These signatures have no instances or coherence tests yet and are not part
-- of the public library contract. Keep them here while exploring those laws.
module MonoidalSketches where

import Cats
import Data.Kind (Constraint)

{- Binary functors: associative, monoidal, braided, symmetric, closed -}

type Braided ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class (Associative p) => Braided (p :: BINARY_OP k) where
  braid :: (x ∈ k, y ∈ k) => k ((x ☼ y) p) ((y ☼ x) p)

type Symmetric ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class (Braided p) => Symmetric p

type BraidedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class
  ( Monoidal p,
    Braided p
  ) =>
  BraidedMonoidal p

type SymmetricMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class
  ( Monoidal p,
    Symmetric p
  ) =>
  SymmetricMonoidal p

type data Twist :: BINARY_OP k -> BINARY_OP k

type instance Act (Twist p) x = Act p '(Snd x, Fst x)

instance (Functor p) => Functor (Twist p) where
  map _ (r :×: l) = map p (l :×: r)

type With₁ p = Curry₂ p

type With₂ p = Curry₂ (Twist p)

type ClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  Constraint
class
  ( forall y. (y ∈ k) => With₂ p y ⊣ With₁ e y,
    Monoidal p
  ) =>
  ClosedMonoidal p (e :: BINARY_OP k)
    | p -> e,
      e -> p

type SymmetricClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  Constraint
class
  ( SymmetricMonoidal p,
    ClosedMonoidal p e
  ) =>
  SymmetricClosedMonoidal p e
    | p -> e,
      e -> p
