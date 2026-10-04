{-# OPTIONS_GHC -Wno-orphans #-}

-- Instances for the example functors used by the lift and traversal tests.
-- They are deliberately test-local; the general Day instances come from Cats.Day.
module DayInstances (Dup) where

import Cats
import Cats.Day
import RecursionSchemes (List)
import Prelude qualified

type Dup = (∧) • Δ₂ Types

instance MonoidObject (Day₁ (∧)) Id where
  empty _ _ = EXP \_ x -> x
  append _ _ = EXP \_ (DataDayTypes xyz fx fy) -> xyz (fx, fy)

instance MonoidObject (Day₁ (∧)) Dup where
  empty _ _ = EXP \_ x -> (x, x)
  append _ _ = EXP \_ (DataDayTypes xyz (fx0, fx1) (fy0, fy1)) ->
    (xyz (fx0, fy0), xyz (fx1, fy1))

instance MonoidObject (Day₁ (∧)) List where
  empty _ _ = EXP \_ x -> [x]
  append _ _ = EXP \_ (DataDayTypes xyz fx fy) ->
    Prelude.liftA2 (\x y -> xyz (x, y)) fx fy
