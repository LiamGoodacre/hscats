module Cats.Adjoint where

import Cats.Category
import Cats.Compose
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

-- Two functors f and g are adjoint when
--   `∀ a b. (a → g b) ⇔ (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) ⇔ d (Act f a) b`
--
-- Typing '⊣': `^q u 22A3` or `^v u 22A3`
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
unit _ a = leftToRight f g (identity (Act f a))

counit ::
  forall {d} g f.
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act (f • g) a) a
counit _ a = rightToLeft g f (identity (Act g a))

join ::
  forall {c} {f} {g}.
  forall (m :: c --> c) a ->
  (m ~ (g • f), f ⊣ g, a ∈ c) =>
  c (Act (m • m) a) (Act m a)
join _ a = map g (counit (f • g) (Act f a))

extend ::
  forall {d} {f} {g}.
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act w a) (Act (w • w) a)
extend _ a = map f (unit (g • f) (Act g a))
