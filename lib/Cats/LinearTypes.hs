{-# OPTIONS_GHC -Wno-orphans #-}

module Cats.LinearTypes
  ( LinearTypes,
  )
where

import Cats.Category
import Cats.Core
import Cats.Semigroupoid
import Data.Kind (FUN, Type)
import Data.Type.Equality (type (~))
import GHC.Base (Multiplicity (..))

-- | Haskell types as objects and functions as arrows.
type LinearTypes = FUN 'One :: CATEGORY Type

type instance Obj LinearTypes t = (t ~ t)

instance Semigroupoid LinearTypes where
  (f ∘ g) x = f (g x)

instance Category LinearTypes where
  identity _ x = x
