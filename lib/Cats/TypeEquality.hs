{-# OPTIONS_GHC -Wno-orphans #-}

module Cats.TypeEquality
  ( (:~:) (Refl),
  )
where

import Cats.Category
import Cats.Core
import Cats.Semigroupoid
import Data.Type.Equality ((:~:) (Refl), type (~))

type instance Obj (:~:) t = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl
