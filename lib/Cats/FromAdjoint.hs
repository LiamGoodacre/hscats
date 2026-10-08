-- | Recognize composites of adjoints and explicitly select their induced
-- monad or comonad structure. 'ViaAdjunction' preserves the object and arrow
-- actions of its argument; it selects instances without imposing a blanket
-- instance on every composed functor.
--
-- If @f ⊣ g@, @ViaAdjunction (g • f)@ is a monad and
-- @ViaAdjunction (f • g)@ is a comonad. Use their operations through
-- "Cats.Monad". The adjunction laws imply the corresponding monoid/comonoid
-- laws; their types alone do not prove those laws.
module Cats.FromAdjoint
  ( AdjunctionMonad,
    AdjunctionMonadBy,
    AdjunctionComonad,
    AdjunctionComonadBy,
    ViaAdjunction,
  )
where

import Cats.Adjoint
import Cats.Category
import Cats.Compose
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Cats.Opposite
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

{- AdjunctionMonad & AdjunctionComonad -}

-- | A composite @g • f@ with @f ⊣ g@ through an explicit intermediate category.
-- This describes the decomposition; use 'ViaAdjunction' to obtain an instance.
type AdjunctionMonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionMonadBy m d =
  ( m ~ TheCompositionBy m d,
    InnerBy m d ⊣ OuterBy m d
  )

-- | 'AdjunctionMonadBy' with the intermediate category inferred from the tag.
type AdjunctionMonad :: (c --> c) -> Constraint
type AdjunctionMonad m = AdjunctionMonadBy m (MidComposition m)

-- | A composite @f • g@ with @f ⊣ g@ through an explicit intermediate category.
type AdjunctionComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d
  )

-- | 'AdjunctionComonadBy' with the intermediate category inferred from the tag.
type AdjunctionComonad :: (c --> c) -> Constraint
type AdjunctionComonad w = AdjunctionComonadBy w (MidComposition w)

-- | Choose the structure induced by an adjunction, without wrapping values.
-- A client may still give the underlying functor its own independent instance.
type data ViaAdjunction :: (c --> c) -> c --> c

type instance Act (ViaAdjunction m) a = Act m a

instance (Functor m) => Functor (ViaAdjunction m) where
  map _ = map m

instance (f ⊣ g) => MonoidObject Composing (ViaAdjunction (g • f)) where
  empty _ _ = EXP \(type a) -> unit (type '(g, f)) a
  append _ _ = EXP \(type a) -> join (type '(g, f)) a

instance (f ⊣ g) => MonoidObject (OpTensor Composing) (ViaAdjunction (f • g)) where
  empty _ _ = OP (EXP \(type a) -> counit (type '(f, g)) a)
  append _ _ = OP (EXP \(type a) -> duplicate (type '(f, g)) a)
