module Cats.MonoidObject where

import Cats.Binary
import Cats.Category
import Cats.Delta
import Cats.Monoidal
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))
import Prelude qualified

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

instance
  (Prelude.Monoid m) =>
  MonoidObject (∧) m
  where
  empty _ _ = \() -> Prelude.mempty
  append _ _ = \(l, r) -> Prelude.mappend l r

mempty :: (MonoidObject (∧) m) => m
mempty = empty (type (∧)) (type _) ()

(<>) :: (MonoidObject (∧) m) => m -> m -> m
l <> r = append (type (∧)) (type _) (l, r)

-- instance
--   ( Monad m,
--     m ~ (f • g)
--   ) =>
--   MonoidObject Composing Id m
--   where
--   empty_ = EXP \_ -> unit m _
--   append_ = EXP \i -> join m i
