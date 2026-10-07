-- | Nullary and binary operations on Day convolution.
--
-- 'Lift0', 'Lift2', and 'LiftN' record operations without requiring functor
-- or monoidal evidence. The specializations below require 'Functor' evidence;
-- 'Alt' supports choice independently of 'Apply', while 'Alternative' requires
-- both the product and coproduct structures.
--
-- To interpret 'LiftN' as a monoid for Day convolution, additionally require
-- @Functor f@ and @Monoidal (Day₁ op)@. Write @t = Day₁ op@, @u = lift0@,
-- and @m = lift2@. Lawful instances satisfy the following equations, with
-- each identity taken at @f@:
--
-- @
-- m ∘ map t (m :×: identity f)
--   = m ∘ map t (identity f :×: m) ∘ rassoc t f f f
-- m ∘ map t (u :×: identity f) = idl
-- m ∘ map t (identity f :×: u) = idr
-- @
--
-- Both operations must be natural transformations. For example, for an
-- arrow @h@ from @a@ to @b@:
--
-- @
-- map f h ∘ (m $$ a) = (m $$ b) ∘ map (Day op f f) h
-- map f h ∘ (u $$ a) = (u $$ b) ∘ map (MonoidalEmpty t) h
-- @
--
-- Over 'Types', multiplication must also respect changes of the hidden Day
-- objects: mapping either input agrees with moving that map into the combining
-- arrow. For appropriately typed @p@, @q@, and @k@:
--
-- @
-- (m $$ z) (DataDayTypes k (map f p x) (map f q y))
--   = (m $$ z) (DataDayTypes (k ∘ map op (p :×: q)) x y)
-- @
--
-- 'Apply' and 'Alt' require natural, associative multiplication compatible
-- with 'map'. 'Applicative' adds the product unit laws; 'Alternative' also
-- adds the coproduct unit laws. These are obligations on instances, not facts
-- established by the types. For general source categories, see the Day
-- representation and associativity restrictions in "Cats.Day".
--
-- 'MonoidObject' carries the additional object and monoidal evidence but also
-- relies on instance authors to obey the laws. The explicit adapters below
-- reuse its operations without introducing blanket lifting instances.
module Cats.Applicative where

import Cats.Binary
import Cats.Category
import Cats.Day
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Cats.Monoidal
import Prelude qualified

-- | Binary multiplication for the source tensor @op@.
class Lift2 (op :: BINARY_OP d) (f :: d --> c) where
  lift2 :: Day op f f ~> f

-- | A map from the Day unit: @pure@ for products, @empty@ for coproducts.
class Lift0 op (f :: d --> c) where
  lift0 :: (MonoidalEmpty (Day₁ op)) ~> f

-- | Both operations, with laws and structural evidence supplied separately.
class (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

instance (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

-- | Reuse a Day monoid's unit in a client-defined 'Lift0' instance or directly.
-- For example, @lift0FromMonoidObject (∧) (type (Constructor [])) $$ Int@ injects an
-- integer into a singleton list using the instance from "Cats.Day".
lift0FromMonoidObject ::
  forall (op :: BINARY_OP d) (f :: d --> c) ->
  (MonoidObject (Day₁ op) f) =>
  MonoidalEmpty (Day₁ op) ~> f
lift0FromMonoidObject op f = empty (Day₁ op) f

-- | Reuse a Day monoid's multiplication without choosing a 'Lift2' instance.
lift2FromMonoidObject ::
  forall (op :: BINARY_OP d) (f :: d --> c) ->
  (MonoidObject (Day₁ op) f) =>
  Day op f f ~> f
lift2FromMonoidObject op f = append (Day₁ op) f

-- special cases

class (Functor f, Lift2 (∧) f) => Apply f

instance (Functor f, Lift2 (∧) f) => Apply f

class (Functor f, LiftN (∧) f) => Applicative f

instance (Functor f, LiftN (∧) f) => Applicative f

class (Functor f, Lift2 (∨) f) => Alt f

instance (Functor f, Lift2 (∨) f) => Alt f

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
