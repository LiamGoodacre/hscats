{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}

module ApplicativeUsage where

import Cats (Constructor)
import Cats.Applicative qualified as A
import Prelude (Int, Maybe (..), String, show, (+))

combinations :: [Int]
combinations = A.liftA2 (type (Constructor [])) (+) [1, 2] [10, 20]

-- [11, 21, 12, 22]

fallback :: Maybe String
fallback =
  A.chooseWith
    (type (Constructor Maybe))
    show
    show
    (Nothing :: Maybe Int)
    (Just 7 :: Maybe Int)

-- Just "7"
