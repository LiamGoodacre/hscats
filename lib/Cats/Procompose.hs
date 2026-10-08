-- | Composition of profunctors, with the outer profunctor first.
--
-- 'procomposeNat' maps both profunctor arguments. 'procomposeLassoc' and
-- 'procomposeRassoc' only rebracket stored values: they preserve the middle
-- objects and all component data, and are inverse even on representatives.
-- Together they satisfy naturality and the pentagon law. 'Procompose₁'
-- exposes these operations as an associative tensor on endoprofunctors.
--
-- The unit is 'Hom'. The four explicit unit maps work for arbitrary
-- categories and lawful profunctors. Removing an inserted unit is identity;
-- inserting a unit after removal need not preserve the raw representative.
-- The latter law uses the coend relation: for @h : m -> n@,
--
-- @
-- MkProcompose (lmap p h pn) qm ~ MkProcompose pn (rmap q h qm)
-- @
--
-- Consumers interpreting the composition coend must respect this relation.
-- Over arbitrary categories the stored intermediate arrows can be inspected,
-- so the representation alone does not enforce it. The 'Monoidal' instance
-- is restricted to 'Types', where total parametric code and lawful functors
-- give the usual extensional interpretation. Unit, triangle, and pentagon
-- equations use that equality, not equality of hidden witness types.
module Cats.Procompose where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.Hom
import Cats.Monoidal
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

-- | Horizontal composition of natural transformations, preserving the
-- intermediate object. The supplied component families must be natural.
procomposeNat ::
  forall {a} {b} {x} (p :: PROFUNCTOR a b) p' (q :: PROFUNCTOR x a) q'.
  (p ~> p') -> (q ~> q') -> Procompose p q ~> Procompose p' q'
procomposeNat left right = EXP \(type ij) (MkProcompose @m pp qq) ->
  MkProcompose @m
    ((left $$ (m, Snd ij)) pp)
    ((right $$ (Fst ij, m)) qq)

-- | Reassociate while retaining both intermediate objects and all three
-- stored components. No coend identification is needed for the inverse law.
procomposeLassoc ::
  forall {a} {b} {c} {x} (p :: PROFUNCTOR b c) (q :: PROFUNCTOR a b) (r :: PROFUNCTOR x a).
  Procompose p (Procompose q r) ~> Procompose (Procompose p q) r
procomposeLassoc = EXP \_ (MkProcompose @m pp (MkProcompose @n qq rr)) ->
  MkProcompose @n (MkProcompose @m pp qq) rr

-- | The inverse of 'procomposeLassoc'.
procomposeRassoc ::
  forall {a} {b} {c} {x} (p :: PROFUNCTOR b c) (q :: PROFUNCTOR a b) (r :: PROFUNCTOR x a).
  Procompose (Procompose p q) r ~> Procompose p (Procompose q r)
procomposeRassoc = EXP \_ (MkProcompose @n (MkProcompose @m pp qq) rr) ->
  MkProcompose @m pp (MkProcompose @n qq rr)

-- | Remove the outer hom profunctor by mapping the output of @p@.
procomposeIdl ::
  forall {a} {b} (p :: PROFUNCTOR a b).
  (Category a, Category b, Profunctor p) => Procompose (Hom b) p ~> p
procomposeIdl = EXP \(type ij) (MkProcompose arrow pp) ->
  map p (OP (identity (Fst ij)) :×: arrow) pp

-- | Insert an outer identity arrow. Removal after insertion is identity;
-- the other round trip uses the coend relation described in the module header.
procomposeCoidl ::
  forall {a} {b} (p :: PROFUNCTOR a b).
  (Category a, Category b, Profunctor p) => p ~> Procompose (Hom b) p
procomposeCoidl = EXP \(type ij) pp ->
  MkProcompose @(Snd ij) (identity (Snd ij)) pp

-- | Remove the inner hom profunctor by mapping the input of @p@.
procomposeIdr ::
  forall {a} {b} (p :: PROFUNCTOR a b).
  (Category a, Category b, Profunctor p) => Procompose p (Hom a) ~> p
procomposeIdr = EXP \(type ij) (MkProcompose pp arrow) ->
  map p (OP arrow :×: identity (Snd ij)) pp

-- | Insert an inner identity arrow; see 'procomposeCoidl' for the laws.
procomposeCoidr ::
  forall {a} {b} (p :: PROFUNCTOR a b).
  (Category a, Category b, Profunctor p) => p ~> Procompose p (Hom a)
procomposeCoidr = EXP \(type ij) pp ->
  MkProcompose @(Fst ij) pp (identity (Fst ij))

-- | Composition as a binary operation on endoprofunctors over @k@.
type data Procompose₁ :: forall k. BINARY_OP (Types ^ (Op k × k))

type instance Act (Procompose₁ @k) pq = Procompose (Fst pq) (Snd pq)

instance (Category k) => Functor (Procompose₁ @k) where
  map _ (left :×: right) = procomposeNat left right

instance (Category k) => Associative (Procompose₁ @k) where
  lassoc _ _ _ _ = procomposeLassoc
  rassoc _ _ _ _ = procomposeRassoc

type instance MonoidalEmpty (Procompose₁ @k) = Hom k

-- Generic unit operations exist above, but a generic Monoidal instance would
-- promise inverse laws that fail for observable raw coend representatives.
instance Monoidal (Procompose₁ @Types) where
  idl = procomposeIdl
  coidl = procomposeCoidl
  idr = procomposeIdr
  coidr = procomposeCoidr
