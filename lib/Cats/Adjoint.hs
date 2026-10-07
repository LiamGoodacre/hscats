module Cats.Adjoint where

import Cats.Category
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

-- | An adjunction gives a natural bijection between @d (Act f a) b@ and
-- @c a (Act g b)@. Write @phi = leftToRight f g@ and
-- @psi = rightToLeft g f@. For arrows between valid objects, instances must
-- satisfy both inverse laws:
--
-- @
-- psi (phi h) = h
-- phi (psi k) = k
-- @
--
-- The bijection must be natural in both endpoints. For @p :: c a' a@ and
-- @q :: d b b'@:
--
-- @
-- phi (q ∘ h ∘ map f p) = map g q ∘ phi h ∘ p
-- psi (map g q ∘ k ∘ p) = q ∘ psi k ∘ map f p
-- @
--
-- These laws imply naturality of 'unit' and 'counit', and the triangle
-- identities documented below. The types and functional dependencies alone
-- do not establish these equations.
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

-- | The unit @eta_a : a -> g (f a)@. For @h :: c a b@, naturality requires
-- @map g (map f h) ∘ eta_a = eta_b ∘ h@.
-- Together with @epsilon = counit@, it satisfies the left triangle:
--
-- @
-- counit (type '(f, g)) (Act f a) ∘ map f (unit (type '(g, f)) a)
--   = identity (Act f a)
-- @
unit ::
  forall {c} {d} (f :: c --> d) (g :: d --> c).
  forall m a ->
  (m ~ '(g, f), f ⊣ g, a ∈ c) =>
  c a (Act g (Act f a))
unit _ (type a) = leftToRight f g (identity (Act f a))

-- | The counit @epsilon_b : f (g b) -> b@. For @h :: d a b@, naturality
-- requires @h ∘ epsilon_a = epsilon_b ∘ map f (map g h)@.
-- The right triangle is:
--
-- @
-- map g (counit (type '(f, g)) b) ∘ unit (type '(g, f)) (Act g b)
--   = identity (Act g b)
-- @
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

duplicate ::
  forall {d} {c} {g :: d --> c} {f :: c --> d}.
  forall w a ->
  (w ~ '(f, g), f ⊣ g, a ∈ d) =>
  d (Act f (Act g a)) (Act f (Act g (Act f (Act g a))))
duplicate _ (type a) = map f (unit (type '(g, f)) (Act g a))
