module Cats.Monoidal where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.Compose
import Cats.Delta
import Cats.Exponential
import Cats.Id
import Data.Kind (Constraint)

type MonoidalEmpty :: BINARY_OP k -> NamesOf k
type family MonoidalEmpty p

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

type instance MonoidalEmpty (∧) = ()

instance Monoidal (∧) where
  idl = \(_, m) -> m
  coidl = \m -> ((), m)
  idr = \(m, _) -> m
  coidr = \m -> (m, ())

type instance MonoidalEmpty Composing = Id

instance
  (Category k) =>
  Monoidal (Composing :: BINARY_OP (k ^ k))
  where
  idl = EXP \_ -> identity _
  coidl = EXP \_ -> identity _
  idr = EXP \_ -> identity _
  coidr = EXP \_ -> identity _
