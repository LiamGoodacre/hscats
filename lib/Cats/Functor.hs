-- | Functor tags, their object action ('Act'), and their arrow action ('map').
-- A tag identifies a functor; values live in its object action. For example,
-- @Constructor []@ is a tag and @Act (Constructor []) Int@ is @[Int]@.
module Cats.Functor where

import Cats.Category
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.Type.Equality (type (~))

infixr 0 -->

-- | Kind of functor tags from a domain category to a codomain category.
type (-->) :: forall i j. CATEGORY i -> CATEGORY j -> Type
type (-->) d c = Proxy d -> Proxy c -> Type

-- | Domain category of a functor tag.
type DomainOf :: forall i (d :: CATEGORY i) c. (d --> c) -> CATEGORY i
type DomainOf (f :: d --> c) = d

-- | Codomain category of a functor tag.
type CodomainOf :: forall j d (c :: CATEGORY j). (d --> c) -> CATEGORY j
type CodomainOf (f :: d --> c) = c

-- | Object action of a functor tag, specified by a type-family equation.
type Act :: (d --> c) -> NamesOf d -> NamesOf c
type family Act f o

-- | Evidence that @Act f o@ is an object of the codomain of @f@.
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
