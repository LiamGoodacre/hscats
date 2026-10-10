{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module SliceUsage where

import Cats
import Data.Kind (Type)
import Prelude qualified as P

type data Length :: Type

instance NamedArrow Types Length where
  type ArrowSource Types Length = P.String
  type ArrowTarget Types Length = P.Int
  namedArrow _ = P.length

type data Number :: Type

instance NamedArrow Types Number where
  type ArrowSource Types Number = P.Int
  type ArrowTarget Types Number = P.Int
  namedArrow _ = P.id

lengthTriangle :: Slice Types P.Int Length Number
lengthTriangle = Slice P.length

example :: P.Int
example = runSlice lengthTriangle "abc"

-- 3
