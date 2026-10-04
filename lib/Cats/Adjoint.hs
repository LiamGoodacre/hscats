module Cats.Adjoint where

import Cats.Category
import Cats.Functor
import Data.Kind (Constraint)
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
  forall {c} {d} (f :: c --> d) (g :: d --> c).
  forall m a ->
  (m ~ '(g, f), f ⊣ g, a ∈ c) =>
  c a (Act g (Act f a))
unit _ (type a) = leftToRight f g (identity (Act f a))

counit ::
  forall {d} {c} (g :: d --> c) (f :: c --> d).
  forall w a ->
  (w ~ '(f, g), f ⊣ g, a ∈ d) =>
  d (Act f (Act g a)) a
counit _ (type a) = rightToLeft g f (identity (Act g a))

join ::
  forall {c} {d} {f :: c --> d} {g :: d --> c}.
  forall m a ->
  (m ~ '(g, f), f ⊣ g, a ∈ c) =>
  c (Act g (Act f (Act g (Act f a)))) (Act g (Act f a))
join _ (type a) = map g (counit (type '(f, g)) (Act f a))

extend ::
  forall {d} {c} {g :: d --> c} {f :: c --> d}.
  forall w a ->
  (w ~ '(f, g), f ⊣ g, a ∈ d) =>
  d (Act f (Act g a)) (Act f (Act g (Act f (Act g a))))
extend _ (type a) = map f (unit (type '(g, f)) (Act g a))
