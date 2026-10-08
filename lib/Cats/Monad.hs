-- | Monads and comonads in an arbitrary category, using the composition tensor.
-- Import this module qualified: its 'unit', 'join', 'counit', and 'duplicate'
-- work with a single functor tag, whereas "Cats.Adjoint" takes a pair of adjoints.
-- The 'Monad' and 'Comonad' constraints, 'flatMap', and 'extend' are also
-- re-exported by "Cats".
--
-- A monad is a 'MonoidObject' for 'Composing'; a comonad is its dual.
-- Their operations must be natural. Writing @eta = unit m@ and @mu = join m@,
-- the monad laws at valid objects are:
--
-- @
-- mu a ∘ eta (Act m a) = identity (Act m a)
-- mu a ∘ map m (eta a) = identity (Act m a)
-- mu a ∘ mu (Act m a) = mu a ∘ map m (mu a)
-- @
--
-- Dually, for @epsilon = counit w@ and @delta = duplicate w@:
--
-- @
-- epsilon (Act w a) ∘ delta a = identity (Act w a)
-- map w (epsilon a) ∘ delta a = identity (Act w a)
-- delta (Act w a) ∘ delta a = map w (delta a) ∘ delta a
-- @
--
-- These specialize the laws in "Cats.MonoidObject"; the constraints supply
-- functor evidence, not proofs. Instances may be defined independently of an
-- adjunction. "Cats.Constructor" lifts ordinary Haskell monads, and
-- "Cats.FromAdjoint" provides an explicit 'Cats.FromAdjoint.ViaAdjunction' tag.
module Cats.Monad
  ( Monad,
    Comonad,
    unit,
    join,
    flatMap,
    counit,
    duplicate,
    extend,
  )
where

import Cats.Category
import Cats.Compose
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Data.Kind (Constraint)

-- | A monoid in the category of endofunctors under composition.
type Monad :: (k --> k) -> Constraint
type Monad m = MonoidObject Composing m

-- | A comonoid in the category of endofunctors under composition.
type Comonad :: (k --> k) -> Constraint
type Comonad w = ComonoidObject Composing w

-- | The monad unit at an object. For @Constructor []@ this makes a singleton.
unit :: forall {k}. forall (m :: k --> k) a -> (Monad m, a ∈ k) => k a (Act m a)
unit m a = empty Composing m $$ a

-- | Flatten two layers of a monad.
join :: forall {k}. forall (m :: k --> k) a -> (Monad m, a ∈ k) => k (Act m (Act m a)) (Act m a)
join m a = append Composing m $$ a

-- | Extend an effectful arrow to monadic inputs (Kleisli extension).
-- Over 'Types', @flatMap (type (Constructor [])) f xs@ is @concatMap f xs@.
flatMap ::
  forall {k} a b.
  forall (m :: k --> k) ->
  (Monad m, a ∈ k, b ∈ k) => k a (Act m b) -> k (Act m a) (Act m b)
flatMap m f = with @(Acts m b) do
  join m b ∘ map m f

-- | Extract a value from a comonad.
counit :: forall {k}. forall (w :: k --> k) a -> (Comonad w, a ∈ k) => k (Act w a) a
counit w a = coempty Composing w $$ a

-- | Duplicate the surrounding context.
duplicate :: forall {k}. forall (w :: k --> k) a -> (Comonad w, a ∈ k) => k (Act w a) (Act w (Act w a))
duplicate w a = coappend Composing w $$ a

-- | Extend a context-consuming arrow to every context (co-Kleisli extension).
extend ::
  forall {k} a b.
  forall (w :: k --> k) ->
  (Comonad w, a ∈ k, b ∈ k) => k (Act w a) b -> k (Act w a) (Act w b)
extend w f = with @(Acts w a) do
  map w f ∘ duplicate w a
