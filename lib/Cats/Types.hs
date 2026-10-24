{-# OPTIONS_GHC -Wno-orphans #-}

module Cats.Types
  ( Types,
  )
where

import Cats.Category
import Cats.Core
import Cats.Semigroupoid
import Data.Kind (Type)
import Data.Type.Equality (type (~))

-- | Haskell types as objects and functions as arrows.
type Types = (->) :: CATEGORY Type

type instance Obj Types t = (t ~ t)

instance Semigroupoid Types where
  (f ∘ g) x = f (g x)

instance Category Types where
  identity _ x = x
