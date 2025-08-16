module Cats.Associative where

import Cats.Binary
import Cats.Category
import Cats.Compose
import Cats.CrossProduct
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

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

instance Associative (∧) where
  lassoc _ _ _ _ = \(a, (b, c)) -> ((a, b), c)
  rassoc _ _ _ _ = \((a, b), c) -> (a, (b, c))

instance (Category k) => Associative (Composing :: BINARY_OP (k ^ k)) where
  lassoc _ _ _ _ = EXP \_ -> identity _
  rassoc _ _ _ _ = EXP \_ -> identity _
