{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE RequiredTypeArguments #-}

module PullbackUsage where

import Cats
import Prelude qualified as P

example :: (P.Int, P.Bool)
example =
  factorPullback
    productPullback
    P.Int
    (Span (P.+ 1) P.even)
    7

-- (8, False)
