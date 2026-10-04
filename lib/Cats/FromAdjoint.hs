module Cats.FromAdjoint
  ( AdjunctionMonad,
    AdjunctionMonadBy,
    AdjunctionComonad,
    AdjunctionComonadBy,
  )
where

import Cats.Adjoint
import Cats.Category
import Cats.Compose
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

{- AdjunctionMonad & AdjunctionComonad -}

type AdjunctionMonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionMonadBy m d =
  ( m ~ TheCompositionBy m d,
    InnerBy m d ⊣ OuterBy m d
  )

type AdjunctionMonad :: (c --> c) -> Constraint
type AdjunctionMonad m = AdjunctionMonadBy m (MidComposition m)

type AdjunctionComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d
  )

type AdjunctionComonad :: (c --> c) -> Constraint
type AdjunctionComonad w = AdjunctionComonadBy w (MidComposition w)
