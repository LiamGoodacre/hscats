module Cats.Applicative where

import Cats.Binary
import Cats.Category
import Cats.Day
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.Monoidal
import Prelude qualified

class Lift2 (op :: BINARY_OP d) (f :: d --> c) where
  lift2 :: Day op f f ~> f

class Lift0 op (f :: d --> c) where
  lift0 :: (MonoidalEmpty (Day₁ op)) ~> f

class (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

instance (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

-- special cases

class (Functor f, Lift2 (∧) f) => Apply f

instance (Functor f, Lift2 (∧) f) => Apply f

class (Functor f, LiftN (∧) f) => Applicative f

instance (Functor f, LiftN (∧) f) => Applicative f

class (Apply f, Lift2 (∨) f) => Alt f

instance (Apply f, Lift2 (∨) f) => Alt f

class (Applicative f, LiftN (∨) f) => Alternative f

instance (Applicative f, LiftN (∨) f) => Alternative f

-- examples

type data List :: Types --> Types

type instance Act List x = [x]

instance Functor List where
  map _ = Prelude.map

-- apply List
instance Lift2 (∧) List where
  lift2 = EXP \_ (DataDayTypes dxyz fx gy) ->
    Prelude.liftA2 (Prelude.curry dxyz) fx gy

-- applicative List
instance Lift0 (∧) List where
  lift0 = EXP \_ -> Prelude.pure

-- alt List
instance Lift2 (∨) List where
  lift2 = EXP \_ (DataDayTypes dxyz fx gy) ->
    Prelude.map (dxyz ∘ Prelude.Left) fx
      Prelude.++ Prelude.map (dxyz ∘ Prelude.Right) gy

-- alternative List
instance Lift0 (∨) List where
  lift0 = EXP \_ () -> []
