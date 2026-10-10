{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}

module DoUsage where

import Cats
import Cats.Do qualified as Do
import Prelude (Int, (+))

example :: [Int]
example = Do.with (type (Constructor [])) Do.do
  x <- [1, 2]
  Do.pure (x + 10)
