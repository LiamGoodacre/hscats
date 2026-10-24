-- | Nullary and binary operations on Day convolution.
--
-- Import this module qualified. It is exposed directly, rather than through
-- "Cats", so names such as 'Applicative', 'pure', and 'empty' are explicit
-- alongside the Prelude and monoid-object APIs. For ordinary type constructors,
-- use 'Constructor'; 'List' is retained as an example of a separate functor tag.
--
-- @
-- {-# LANGUAGE GHC2024, RequiredTypeArguments, TypeAbstractions #-}
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
-- To define a client tag, implement 'Lift0' and/or 'Lift2' for the desired
-- tensor, and 'Functor' for the specializations. The blanket instances derive
-- 'LiftN', 'Apply', 'Applicative', 'Alt', and 'Alternative'; clients do not
-- define competing instances for those constraint classes. Generic lifting
-- operations allow any source and target categories. The product/coproduct
-- specializations fix the source to 'Types'; the value helpers also fix the
-- target to 'Types'.
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
module Cats.Applicative
  ( Lift0 (..),
    Lift2 (..),
    LiftN,
    Apply,
    Applicative,
    Alt,
    Alternative,
    lift0FromMonoidObject,
    lift2FromMonoidObject,
    pure,
    liftA2,
    apply,
    keepLeft,
    keepRight,
    blank,
    chooseWith,
    choose,
    MonoidObjectFromLiftN,
  )
where

import Cats.Binary
import Cats.Core
import Cats.Day
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject (MonoidObject)
import Cats.MonoidObject qualified as Monoid
import Cats.Monoidal
import Cats.Semigroupoid
import Cats.Types
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))
import Prelude qualified

-- | Binary multiplication for the source tensor @op@.
type Lift2 :: BINARY_OP d -> (d --> c) -> Constraint
class Lift2 (op :: BINARY_OP d) (f :: d --> c) where
  lift2 :: forall op' f' -> (op' ~ op, f' ~ f) => Day op f f ~> f

-- | A map from the Day unit: @pure@ for products, @empty@ for coproducts.
type Lift0 :: BINARY_OP d -> (d --> c) -> Constraint
class Lift0 op (f :: d --> c) where
  lift0 :: forall op' f' -> (op' ~ op, f' ~ f) => (MonoidalEmpty (Day₁ op)) ~> f

-- | Both operations, with laws and structural evidence supplied separately.
type LiftN :: BINARY_OP d -> (d --> c) -> Constraint
class (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

instance (Lift0 op f, Lift2 op f) => LiftN op (f :: d --> c)

-- special cases

-- | Functorial, associative product combination, without requiring a unit.
-- Use 'liftA2' for ordinary values over 'Types'.
type Apply :: (Types --> c) -> Constraint
class (Functor f, Lift2 (∧) f) => Apply f

instance (Functor f, Lift2 (∧) f) => Apply f

-- | 'Apply' with a product unit satisfying the laws in the module header.
-- The blanket instances derive 'Apply' from this constraint.
type Applicative :: (Types --> c) -> Constraint
class (Functor f, LiftN (∧) f) => Applicative f

instance (Functor f, LiftN (∧) f) => Applicative f

-- | Functorial, associative choice, independently of product combination.
-- Use 'chooseWith' to map both alternatives to a common result type.
type Alt :: (Types --> c) -> Constraint
class (Functor f, Lift2 (∨) f) => Alt f

instance (Functor f, Lift2 (∨) f) => Alt f

-- | 'Applicative' together with 'Alt' and a choice unit. The two structures
-- satisfy their separate monoid laws; no extra interaction laws are assumed.
type Alternative :: (Types --> c) -> Constraint
class (Applicative f, LiftN (∨) f) => Alternative f

instance (Applicative f, LiftN (∨) f) => Alternative f

-- | Lift a value using just the product unit. No binary operation or functor
-- constraint is needed; an 'Applicative' instance supplies this operation.
pure :: forall a. forall (f :: Types --> Types) -> (Lift0 (∧) f) => a -> Act f a
pure f = member (type Types) a do
  run (lift0 (type (∧)) (type f)) a

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
        (lift2 (type (∧)) (type f) $$ c) (DataDayTypes (Prelude.uncurry combine) left right)

-- | Apply wrapped functions to wrapped arguments. Uses only 'Apply'.
-- For lists, functions form the outer loop and arguments the inner loop.
apply ::
  forall a b.
  forall (f :: Types --> Types) ->
  (Apply f) => Act f (a -> b) -> Act f a -> Act f b
apply f = liftA2 @(a -> b) @a @b f (Prelude.$)

-- | Combine both effects and retain the left result, using only 'Apply'.
-- Lists repeat each left value once per right value; either empty input gives
-- an empty result. Optional values require both inputs to be present.
-- Effect order and strictness are those of the instance's 'liftA2'.
keepLeft ::
  forall a b.
  forall (f :: Types --> Types) ->
  (Apply f) => Act f a -> Act f b -> Act f a
keepLeft f = liftA2 @a @b @a f Prelude.const

-- | Combine both effects and retain the right result, using only 'Apply'.
-- Lists repeat the entire right list for each left value. Optional values
-- require both inputs to be present. Discarding a result does not remove its
-- effect; effect order and strictness follow the instance's 'liftA2'.
keepRight ::
  forall a b.
  forall (f :: Types --> Types) ->
  (Apply f) => Act f a -> Act f b -> Act f b
keepRight f = liftA2 @a @b @b f (\_ right -> right)

-- | The empty choice, using just the coproduct unit. An 'Alternative'
-- instance supplies this operation, but its product operations are not needed.
blank :: forall a. forall (f :: Types --> Types) -> (Lift0 (∨) f) => Act f a
blank f = member (type Types) a do
  run (lift0 (type (∨)) (type f)) a ()

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
        (lift2 (type (∨)) (type f) $$ c) (DataDayTypes (Prelude.either leftMap rightMap) left right)

-- | Combine alternatives with the same result type, using only 'Alt'.
-- Lists concatenate in input order. Optional values prefer the left input
-- and inspect the right only if the left is absent.
choose ::
  forall a.
  forall (f :: Types --> Types) ->
  (Alt f) => Act f a -> Act f a -> Act f a
choose f = chooseWith @a @a @a f Prelude.id Prelude.id

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

type data
  MonoidObjectFromLiftN ::
    BINARY_OP d ->
    (d --> c) ->
    (d --> c)

type instance Act (MonoidObjectFromLiftN op f) o = Act f o

instance (Functor f) => Functor (MonoidObjectFromLiftN op f) where
  map _ = map f

instance
  ( Functor f,
    Monoidal (Day₁ @Types @Types op),
    LiftN op f
  ) =>
  MonoidObject
    (Day₁ @Types @Types op)
    (MonoidObjectFromLiftN op f)
  where
  empty _ _ = castExp ∘ lift0 (type op) (type f)
  append _ _ = castExp ∘ lift2 (type op) (type f) ∘ castDay
