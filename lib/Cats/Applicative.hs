-- | Nullary and binary operations on Day convolution.
--
-- Import this module qualified. It is exposed directly, rather than through
-- "Cats", so names such as 'Applicative', 'pure', and 'empty' are explicit
-- alongside the Prelude and monoid-object APIs. For ordinary type constructors,
-- use 'Constructor'; 'List' is retained as an example of a separate functor tag.
--
-- @
-- {-# LANGUAGE RequiredTypeArguments, TypeAbstractions #-}
-- import Cats (Constructor)
-- import Cats.Applicative qualified as A
-- import Prelude (Int, Maybe(..), String, (+), show)
--
-- combinations :: [Int]
-- combinations = A.liftA2 (type (Constructor [])) (+) [1, 2] [10, 20]
-- -- [11, 21, 12, 22]
--
-- fallback :: Maybe String
-- fallback = A.chooseWith (type (Constructor Maybe)) show show
--              (Nothing :: Maybe Int) (Just 7 :: Maybe Int)
-- -- Just "7"
-- @
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
-- 'Alternative' combines the two structures without imposing additional
-- distributivity or annihilation laws between them. For example, the list
-- result of @Prelude.liftA2 (+) [1,2] ([10] ++ [20])@ is @[11,21,12,22]@,
-- whereas choosing between the two separate products gives @[11,12,21,22]@.
-- An extra distributivity requirement would therefore exclude this instance.
--
-- 'MonoidObject' carries the additional object and monoidal evidence but also
-- relies on instance authors to obey the laws. The explicit adapters below
-- reuse its operations without introducing blanket lifting instances.
module Cats.Applicative where

import Cats.Binary
import Cats.Category
import Cats.Constructor
import Cats.Day
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject (MonoidObject)
import Cats.MonoidObject qualified as Monoid
import Cats.Monoidal
import Control.Applicative qualified as Prelude
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
lift0FromMonoidObject op f = Monoid.empty (Day₁ op) f

-- | Reuse a Day monoid's multiplication without choosing a 'Lift2' instance.
lift2FromMonoidObject ::
  forall (op :: BINARY_OP d) (f :: d --> c) ->
  (MonoidObject (Day₁ op) f) =>
  Day op f f ~> f
lift2FromMonoidObject op f = Monoid.append (Day₁ op) f

-- special cases

-- | Functorial, associative product combination, without requiring a unit.
-- Use 'liftA2' for ordinary values over 'Types'.
class (Functor f, Lift2 (∧) f) => Apply f

instance (Functor f, Lift2 (∧) f) => Apply f

-- | 'Apply' with a product unit satisfying the laws in the module header.
-- The blanket instances derive 'Apply' from this constraint.
class (Functor f, LiftN (∧) f) => Applicative f

instance (Functor f, LiftN (∧) f) => Applicative f

-- | Functorial, associative choice, independently of product combination.
-- Use 'chooseWith' to map both alternatives to a common result type.
class (Functor f, Lift2 (∨) f) => Alt f

instance (Functor f, Lift2 (∨) f) => Alt f

-- | 'Applicative' together with 'Alt' and a choice unit. The two structures
-- satisfy their separate monoid laws; no extra interaction laws are assumed.
class (Applicative f, LiftN (∨) f) => Alternative f

instance (Applicative f, LiftN (∨) f) => Alternative f

-- | Lift a value using just the product unit. No binary operation or functor
-- constraint is needed; an 'Applicative' instance supplies this operation.
pure :: forall a. forall (f :: Types --> Types) -> (Lift0 (∧) f) => a -> Act f a
pure f = member (type Types) a do
  lift0 @_ @_ @(∧) @f $$ a

-- | Combine two values with a binary function. Requires 'Apply', so a unit
-- instance is unnecessary. For lists, the left input is the outer loop.
liftA2 ::
  forall a b c.
  forall (f :: Types --> Types) ->
  (Apply f) => (a -> b -> c) -> Act f a -> Act f b -> Act f c
liftA2 f combine left right =
  member (type Types) a do
    member (type Types) b do
      member (type Types) c do
        (lift2 @_ @_ @(∧) @f $$ c) (DataDayTypes (Prelude.uncurry combine) left right)

-- | The empty choice, using just the coproduct unit. An 'Alternative'
-- instance supplies this operation, but its product operations are not needed.
empty :: forall a. forall (f :: Types --> Types) -> (Lift0 (∨) f) => Act f a
empty f = member (type Types) a do
  (lift0 @_ @_ @(∨) @f $$ a) ()

-- | Map two alternatives to a common result and combine them. Requires only
-- 'Alt'; neither product combination nor an empty choice is needed.
-- For 'Constructor' lists this concatenates the mapped values; for 'Prelude.Maybe'
-- it selects the first present alternative.
chooseWith ::
  forall a b c.
  forall (f :: Types --> Types) ->
  (Alt f) => (a -> c) -> (b -> c) -> Act f a -> Act f b -> Act f c
chooseWith f leftMap rightMap left right =
  member (type Types) a do
    member (type Types) b do
      member (type Types) c do
        (lift2 @_ @_ @(∨) @f $$ c) (DataDayTypes (Prelude.either leftMap rightMap) left right)

-- Specific heads let clients keep independent instances for their own tags.
instance (Prelude.Applicative f) => Lift0 (∧) (Constructor f) where
  lift0 = lift0FromMonoidObject (∧) (type (Constructor f))

instance (Prelude.Applicative f) => Lift2 (∧) (Constructor f) where
  lift2 = lift2FromMonoidObject (∧) (type (Constructor f))

instance (Prelude.Alternative f) => Lift0 (∨) (Constructor f) where
  lift0 = lift0FromMonoidObject (∨) (type (Constructor f))

instance (Prelude.Alternative f) => Lift2 (∨) (Constructor f) where
  lift2 = lift2FromMonoidObject (∨) (type (Constructor f))

-- examples

-- | Example of a fresh functor tag with its own 'Act' equation. Its lifting
-- operations reuse 'Constructor' lists, so there is one implementation of
-- list behavior. Prefer @Constructor []@ in client code.
type data List :: Types --> Types

type instance Act List x = [x]

instance Functor List where
  map _ = Prelude.map

-- apply List
instance Lift2 (∧) List where
  lift2 = EXP \_ (DataDayTypes dxyz fx gy) ->
    liftA2 (type (Constructor [])) (Prelude.curry dxyz) fx gy

-- applicative List
instance Lift0 (∧) List where
  lift0 = EXP \_ -> pure (type (Constructor []))

-- alt List
instance Lift2 (∨) List where
  lift2 = EXP \_ (DataDayTypes dxyz fx gy) ->
    chooseWith (type (Constructor [])) (dxyz ∘ Prelude.Left) (dxyz ∘ Prelude.Right) fx gy

-- alternative List
instance Lift0 (∨) List where
  lift0 = EXP \_ () -> empty (type (Constructor []))
