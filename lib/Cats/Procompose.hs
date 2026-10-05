module Cats.Procompose where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Cats.Opposite
import Cats.Profunctor
import Data.Kind (Type)

-- | Two profunctor values joined at an existential intermediate object.
-- A value of q goes from i to m, followed by a value of p from m to j.
-- This stores a representative of the composition coend; it does not quotient
-- representatives by moving intermediate arrows between the two values.
data
  DataProcompose ::
    PROFUNCTOR a b ->
    PROFUNCTOR x a ->
    NamesOf x ->
    NamesOf b ->
    Type
  where
  MkProcompose ::
    forall m i j p q.
    ( '(m, j) ∈ DomainOf p,
      '(i, m) ∈ DomainOf q
    ) =>
    Act p '(m, j) ->
    Act q '(i, m) ->
    DataProcompose p q i j

-- | Profunctor composition, with the outer profunctor first.
type data Procompose :: PROFUNCTOR a b -> PROFUNCTOR x a -> PROFUNCTOR x b

type instance Act (Procompose p q) '(i, j) = DataProcompose p q i j

instance
  (Category a, Category b, Category x, Profunctor p, Profunctor q) =>
  Functor (Procompose (p :: PROFUNCTOR a b) (q :: PROFUNCTOR x a))
  where
  map _ (OP l :×: r) (MkProcompose @m pp qq) =
    -- Keep the intermediate object fixed. Supplying its identity explicitly
    -- determines the indices even when the component Act families are not injective.
    MkProcompose @m
      (map p (OP (identity m) :×: r) pp)
      (map q (OP l :×: identity m) qq)
