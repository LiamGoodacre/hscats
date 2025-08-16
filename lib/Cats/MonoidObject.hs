module Cats.MonoidObject where

import Cats.Binary
import Cats.Category
import Cats.Delta
import Cats.Monoidal
import Data.Kind (Constraint)
import Prelude qualified

type MonoidObject ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  i ->
  Constraint
class
  ( Monoidal p id,
    m ∈ k
  ) =>
  MonoidObject (p :: BINARY_OP k) id m
    | p -> id
  where
  empty_ :: k id m
  append_ :: k ((m ☼ m) p) m

empty ::
  forall {i} {k :: CATEGORY i} (p :: BINARY_OP k) {id :: i} (m :: i).
  (MonoidObject p id m) =>
  k id m
empty = empty_ @k @p @id @m

append ::
  forall {i} {k :: CATEGORY i} (p :: BINARY_OP k) {id :: i} (m :: i).
  (MonoidObject p id m) =>
  k ((☼) m m p) m
append = append_ @k @p @id @m

instance
  (Prelude.Monoid m) =>
  MonoidObject (∧) () m
  where
  empty_ = \() -> Prelude.mempty
  append_ = \(l, r) -> Prelude.mappend l r

mempty :: (MonoidObject (∧) () m) => m
mempty = empty @(∧) ()

(<>) :: (MonoidObject (∧) () m) => m -> m -> m
l <> r = append @(∧) (l, r)

-- instance
--   (Prelude.Applicative m) =>
--   MonoidObject (Day (∧)) Id m
--   where
--   empty_ = EXP \_ -> undefined
--   append_ = EXP \_ -> undefined

-- instance
--   ( Monad m,
--     m ~ (f • g)
--   ) =>
--   MonoidObject Composing Id m
--   where
--   empty_ = EXP \_ -> unit m _
--   append_ = EXP \i -> join m i
