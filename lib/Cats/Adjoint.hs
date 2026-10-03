module Cats.Adjoint where

import Cats.Category
import Cats.Compose
import Cats.Functor
import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (~))

-- Two functors f and g are adjoint when
--   `∀ a b. (a → g b) ⇔ (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) ⇔ d (Act f a) b`
--
-- Typing '⊣': ` u 22a3` or ` u 22a3`
--
type (⊣) :: forall d c. (c --> d) -> (d --> c) -> Constraint
class (Functor f, Functor g) => (⊣) @d @c f g | f -> g, g -> f where
  rightToLeft ::
    forall g' f' ->
    (f' ~ f, g' ~ g, a ∈ c, b ∈ d) =>
    c a (Act g b) -> d (Act f a) b
  leftToRight ::
    forall f' g' ->
    (f' ~ f, g' ~ g, a ∈ c, b ∈ d) =>
    d (Act f a) b -> c a (Act g b)

unit ::
  forall {c} f g.
  forall (m :: c --> c) a ->
  (m ~ (g • f), f ⊣ g, a ∈ c) =>
  c a (Act (g • f) a)
unit _ (type a) = leftToRight f g (identity (Act f a))

counit ::
  forall {d} g f.
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act (f • g) a) a
counit _ (type a) = rightToLeft g f (identity (Act g a))

join ::
  forall {c} {f} {g}.
  forall (m :: c --> c) a ->
  (m ~ (g • f), f ⊣ g, a ∈ c) =>
  c (Act (m • m) a) (Act m a)
join _ (type a) = map g (counit (f • g) (Act f a))

extend ::
  forall {d} {f} {g}.
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act w a) (Act (w • w) a)
extend _ (type a) = map f (unit (g • f) (Act g a))

{- Monad & Comonad -}

type MidCompositionIx :: forall c. (c --> c) -> Type
type family MidCompositionIx m where
  MidCompositionIx (g • f) = NamesOf (DomainOf g)

type MidComposition :: forall c. forall (m :: c --> c) -> CATEGORY (MidCompositionIx m)
type family MidComposition m where
  MidComposition (g • f) = DomainOf g

type OuterBy :: (c --> c) -> forall (d :: CATEGORY i) -> (d --> c)
type family OuterBy m d where
  OuterBy (g • f) d = g

type InnerBy :: (c --> c) -> forall (d :: CATEGORY i) -> (c --> d)
type family InnerBy m d where
  InnerBy (g • f) d = f

type Inner :: forall (m :: c --> c) -> (c --> MidComposition m)
type Inner m = InnerBy m (MidComposition m)

type Outer :: forall (m :: c --> c) -> (MidComposition m --> c)
type Outer m = OuterBy m (MidComposition m)

type TheCompositionBy :: (c --> c) -> CATEGORY i -> (c --> c)
type TheCompositionBy m d = OuterBy m d • InnerBy m d

type TheComposition :: (c --> c) -> (c --> c)
type TheComposition m = TheCompositionBy m (MidComposition m)

type MonadBy :: (c --> c) -> CATEGORY i -> Constraint
type MonadBy m d =
  ( m ~ TheCompositionBy m d,
    InnerBy m d ⊣ OuterBy m d
  )

type Monad :: (c --> c) -> Constraint
type Monad m = MonadBy m (MidComposition m)

type ComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type ComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d
  )

type Comonad :: (c --> c) -> Constraint
type Comonad w = ComonadBy w (MidComposition w)

type Invert :: forall c. forall (m :: c --> c) -> (MidComposition m --> MidComposition m)
type Invert m = Inner m • Outer m
