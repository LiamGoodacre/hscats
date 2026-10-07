module Cats.Functor where

import Cats.Category
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.Type.Equality (type (~))

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

-- | A functor acts on objects via 'Act' and on arrows via 'map'. It must
-- preserve identities and composition between valid objects:
--
-- @
-- map f (identity a) = identity (Act f a)
-- map f (h ∘ g) = map f h ∘ map f g
-- @
--
-- The superclasses ensure that the domain and codomain are categories and
-- that valid domain objects map to valid codomain objects. Instance authors
-- must establish the equations separately.
type Functor :: (d --> c) -> Constraint
class
  ( Category d,
    Category c,
    forall o. (o ∈ DomainOf f) => Acts f o
  ) =>
  Functor (f :: d --> c)
  where
  map ::
    forall f' ->
    (f' ~ f, a ∈ d, b ∈ d) =>
    d a b -> c (Act f a) (Act f b)

-- Sometimes GHC needs a hint as to how to bring
-- `Act f i ∈ CodomainOf f` into scope.
acting ::
  forall f i ->
  ( Functor f,
    i ∈ DomainOf f
  ) =>
  ((Act f i ∈ CodomainOf f) => r) -> r
acting _ _ r = r
