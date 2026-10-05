module Cats.Yoneda where

import Cats.Category
import Cats.Curry
import Cats.Exponential
import Cats.Flip
import Cats.Functor
import Cats.Hom
import Cats.Opposite

-- Λo . Λi . c(i, o)
type YonedaEmbedding :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type YonedaEmbedding c = Curry₁ (Flip (Hom c))

-- o ⊢ Λi . c(i, o)
type HomTo :: forall (c :: CATEGORY o) -> NamesOf c -> Op c --> Types
type HomTo c = Curry₂ (Flip (Hom c))

-- Λi . Λo . c(i, o)
type CoyonedaEmbedding :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type CoyonedaEmbedding c = Curry₁ (Hom c)

-- i ⊢ Λo . c(i, o)
type HomFrom :: forall (c :: CATEGORY o) -> NamesOf (Op c) -> c --> Types
type HomFrom c = Curry₂ (Hom c)
