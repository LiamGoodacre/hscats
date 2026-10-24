module Cats.Symmetric where

import Cats.Binary
import Cats.Core
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

type Symmetric ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class Symmetric (op :: BINARY_OP k) where
  symm ::
    forall op' l r ->
    (op' ~ op) =>
    (l ∈ k, r ∈ k) =>
    k ((l ☼ r) op) ((r ☼ l) op)
