module Cats.Monoidal where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.Compose
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.Id
import Data.Kind (Constraint)

type Monoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  Constraint
class
  (Associative p) =>
  Monoidal (p :: BINARY_OP k) id
    | p -> id
  where
  idl :: (m ∈ k) => k ((id ☼ m) p) m
  coidl :: (m ∈ k) => k m ((id ☼ m) p)
  idr :: (m ∈ k) => k ((m ☼ id) p) m
  coidr :: (m ∈ k) => k m ((m ☼ id) p)

instance Monoidal (∧) () where
  idl = \(_, m) -> m
  coidl = \m -> ((), m)
  idr = \(m, _) -> m
  coidr = \m -> (m, ())

instance
  (Category k) =>
  Monoidal Composing (Id :: k --> k)
  where
  idl = EXP \_ -> identity _
  coidl = EXP \_ -> identity _
  idr = EXP \_ -> identity _
  coidr = EXP \_ -> identity _
