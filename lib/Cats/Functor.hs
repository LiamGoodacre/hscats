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

class TrivialSuper f

instance TrivialSuper f

type Super :: forall d c. (d --> c) -> Constraint
type family Super @d @c

type instance Super @Types = TrivialSuper

-- What is a functor?
-- DomainOf must be a category.
-- CodomainOf must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
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
