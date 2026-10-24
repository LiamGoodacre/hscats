module Cats.TypeConstructor where

import Cats.Applicative
import Cats.Compose
import Cats.Day
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Cats.Semigroupoid
import Cats.Types
import Control.Applicative qualified as Prelude
import Data.Kind (Type)
import Prelude qualified

type data TypeConstructor (f :: Type -> Type) :: Types --> Types

type instance Act (TypeConstructor f) a = f a

instance (Prelude.Functor f) => Functor (TypeConstructor f) where
  map _ = Prelude.fmap

instance (Prelude.Applicative f) => Lift0 (∧) (TypeConstructor f) where
  lift0 _ _ = EXP \_ -> Prelude.pure

instance (Prelude.Applicative f) => Lift2 (∧) (TypeConstructor f) where
  lift2 = EXP \_ (DataDayTypes o l r) ->
    Prelude.liftA2 (Prelude.curry o) l r

instance
  (Prelude.Applicative m) =>
  MonoidObject (Day₁ @Types @Types (∧)) (TypeConstructor m)
  where
  empty _ _ = EXP \_ -> Prelude.pure
  append _ _ = EXP \_ (DataDayTypes xyz mx my) -> Prelude.liftA2 (\x y -> xyz (x, y)) mx my

instance (Prelude.Alternative f) => Lift0 (∨) (TypeConstructor f) where
  lift0 _ _ = EXP \_ () -> Prelude.empty

instance (Prelude.Alternative f) => Lift2 (∨) (TypeConstructor f) where
  lift2 = EXP \_ (DataDayTypes o l r) -> do
    let lhs = (o ∘ Prelude.Left) Prelude.<$> l
    let rhs = (o ∘ Prelude.Right) Prelude.<$> r
    lhs Prelude.<|> rhs

instance
  (Prelude.Alternative m) =>
  MonoidObject (Day₁ @Types @Types (∨)) (TypeConstructor m)
  where
  empty _ _ = EXP \_ () -> Prelude.empty
  append _ _ = EXP \_ (DataDayTypes doxyz mx my :: DataDay (∨) f g z) ->
    map f (doxyz ∘ Prelude.Left) mx Prelude.<|> map g (doxyz ∘ Prelude.Right) my

instance (Prelude.Monad f) => MonoidObject Composing (TypeConstructor f) where
  empty _ _ = EXP \_ -> Prelude.pure
  append _ _ = EXP \_ mm -> mm Prelude.>>= Prelude.id
