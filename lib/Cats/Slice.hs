-- | Slice and coslice categories whose objects name particular arrows.
--
-- Object tags distinguish different arrows with the same endpoints, just as
-- functor tags distinguish different object and arrow actions. Each
-- 'NamedArrow' instance selects one arrow. A t'Slice' or t'Coslice' arrow must
-- satisfy its commuting-triangle law; the constructor cannot prove that law.
-- Identities and composition preserve lawful triangles.
--
-- @
-- {-# LANGUAGE GHC2024, RequiredTypeArguments, TypeAbstractions, TypeData, TypeFamilies #-}
-- import Cats
-- import Data.Kind (Type)
-- import Prelude qualified as P
--
-- type data Length :: Type
-- instance NamedArrow Types Length where
--   type ArrowSource Types Length = P.String
--   type ArrowTarget Types Length = P.Int
--   namedArrow _ = P.length
--
-- type data Number :: Type
-- instance NamedArrow Types Number where
--   type ArrowSource Types Number = P.Int
--   type ArrowTarget Types Number = P.Int
--   namedArrow _ = P.id
--
-- lengthTriangle :: Slice Types P.Int Length Number
-- lengthTriangle = Slice P.length
--
-- example :: P.Int
-- example = runSlice lengthTriangle "abc"
-- -- 3
-- @
module Cats.Slice where

import Cats.Category
import Cats.Functor
import Data.Kind (Type)
import Data.Type.Equality (type (~))

-- | A tag naming a specific arrow, with valid source and target objects.
-- Define the two associated object names and supply 'namedArrow'. The object
-- names of @k@ can have any kind, while the tags themselves have kind 'Type'.
class
  (Category k, ArrowSource k f ∈ k, ArrowTarget k f ∈ k) =>
  NamedArrow (k :: CATEGORY i) (f :: Type)
  where
  type ArrowSource k f :: i
  type ArrowTarget k f :: i
  namedArrow :: forall f' -> (f' ~ f) => k (ArrowSource k f) (ArrowTarget k f)

-- | The slice @k / z@. Objects are tags for arrows into @z@.
-- A lawful @Slice h :: Slice k z f g@ satisfies
-- @namedArrow g ∘ h = namedArrow f@. Parallel slice arrows are equal when
-- their underlying arrows are equal in @k@.
data Slice (k :: CATEGORY i) (z :: i) (f :: Type) (g :: Type) where
  Slice :: {runSlice :: k (ArrowSource k f) (ArrowSource k g)} -> Slice k z f g

type instance Obj (Slice k z) f = (NamedArrow k f, ArrowTarget k f ~ z)

instance (Semigroupoid k) => Semigroupoid (Slice k z) where
  Slice h ∘ Slice g = Slice (h ∘ g)

instance (Category k) => Category (Slice k z) where
  identity f = Slice (identity (ArrowSource k f))

-- | The coslice @z / k@. Objects are tags for arrows out of @z@.
-- A lawful @Coslice h :: Coslice k z f g@ satisfies
-- @h ∘ namedArrow f = namedArrow g@. Equality is inherited from @k@.
data Coslice (k :: CATEGORY i) (z :: i) (f :: Type) (g :: Type) where
  Coslice :: {runCoslice :: k (ArrowTarget k f) (ArrowTarget k g)} -> Coslice k z f g

type instance Obj (Coslice k z) f = (NamedArrow k f, ArrowSource k f ~ z)

instance (Semigroupoid k) => Semigroupoid (Coslice k z) where
  Coslice h ∘ Coslice g = Coslice (h ∘ g)

instance (Category k) => Category (Coslice k z) where
  identity f = Coslice (identity (ArrowTarget k f))

-- | Forget a slice object's chosen arrow, retaining its domain.
type data SliceDomain :: forall (k :: CATEGORY i) (z :: i) -> Slice k z --> k

type instance Act (SliceDomain k z) f = ArrowSource k f

instance (Category k) => Functor (SliceDomain k z) where
  map _ (Slice h) = h

-- | Forget a coslice object's chosen arrow, retaining its codomain.
type data CosliceCodomain :: forall (k :: CATEGORY i) (z :: i) -> Coslice k z --> k

type instance Act (CosliceCodomain k z) f = ArrowTarget k f

instance (Category k) => Functor (CosliceCodomain k z) where
  map _ (Coslice h) = h
