module Cats.MonoidObject where

import Cats.Binary
import Cats.Category
import Cats.Monoidal
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

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
