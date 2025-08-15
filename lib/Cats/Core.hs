module Cats.Core where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.Type.Equality ((:~:) (Refl), type (~))
import Prelude qualified

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Lookup the type of a category's object names
type NamesOf :: forall i. CATEGORY i -> Type
type NamesOf @i c = i

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k

-- Semigroupoids have a means of composing arrows
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- Categories are Semigroupoids with an identity arrow
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o

-- Type of functors indexed by domain & codomain categories
type (-->) :: forall i j. CATEGORY i -> CATEGORY j -> Type
type (-->) d c = Proxy d -> Proxy c -> Type

-- Project the domain category of a functor
type DomainOf :: forall i (d :: CATEGORY i) c. (d --> c) -> CATEGORY i
type DomainOf (f :: d --> c) = d

-- Project the codomain category of a functor
type CodomainOf :: forall j d (c :: CATEGORY j). (d --> c) -> CATEGORY j
type CodomainOf (f :: d --> c) = c

-- Functors act on object names
type Act :: (d --> c) -> NamesOf d -> NamesOf c
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ CodomainOf f) => Acts f o

instance (Act f o ∈ CodomainOf f) => Acts f o

-- What is a functor?
-- DomainOf must be a category.
-- CodomainOf must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
type Functor :: (d --> c) -> Constraint
class (Category d, Category c, forall o. (o ∈ DomainOf f) => Acts f o) => Functor (f :: d --> c) where
  map ::
    forall f' ->
    (f' ~ f, a ∈ d, b ∈ d) =>
    d a b -> c (Act f a) (Act f b)

-- Two functors f and g are adjoint when
--   `∀ a b. (a → g b) ⇔ (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) ⇔ d (Act f a) b`
--
-- Typing '⊣': `^q u 22A3` or `^v u 22A3`
--

type (⊣) :: (c --> d) -> (d --> c) -> Constraint
class
  (Functor f, Functor g) =>
  f ⊣ (g :: d --> c)
    | f -> g,
      g -> f
  where
  leftAdjoint ::
    forall g' f' ->
    (f' ~ f, g' ~ g) =>
    (a ∈ c, b ∈ d) =>
    c a (Act g b) ->
    d (Act f a) b
  rightAdjoint ::
    forall f' g' ->
    (f' ~ f, g' ~ g) =>
    (a ∈ c, b ∈ d) =>
    d (Act f a) b ->
    c a (Act g b)

-- "Equality" forms a category
type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl

-- "Type" forms a category
type Types = (->) :: CATEGORY Type

type instance t ∈ Types = (t ~ t)

instance Semigroupoid Types where
  (∘) = (Prelude..)

instance Category Types where
  identity _ = Prelude.id
