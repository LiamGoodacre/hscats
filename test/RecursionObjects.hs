-- | Object references used by the active recursion-scheme checks.
module RecursionObjects (OBJECT, ObjectName, AnObject) where

import Cats.Category
import Data.Kind (Type)
import Data.Proxy (Proxy)

{- Referencing special objects -}

type OBJECT :: forall i. CATEGORY i -> Type
type OBJECT k = Proxy k -> Type

type ObjectName :: OBJECT k -> NamesOf k
type family ObjectName o

type data AnObject :: forall (k :: CATEGORY i) -> NamesOf k -> OBJECT k

type instance ObjectName (AnObject k n) = n
