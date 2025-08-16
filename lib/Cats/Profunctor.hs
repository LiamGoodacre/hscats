module Cats.Profunctor where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor

newtype Viewer :: CATEGORY o -> CATEGORY (o, o) where
  Viewer :: {runViewer :: k (Fst st) (Fst ab)} -> Viewer k ab st

type instance o ∈ Viewer k = (o ∈ (k × k))

instance (Semigroupoid k) => Semigroupoid (Viewer k) where
  Viewer f ∘ Viewer g = Viewer (g ∘ f)

instance (Category k) => Category (Viewer k) where
  identity _ = Viewer (identity _)

data Like :: CATEGORY o -> CATEGORY (o, o) where
  Like ::
    !(k (Fst st) (Fst ab)) ->
    !(k (Snd ab) (Snd st)) ->
    Like k ab st

type instance o ∈ Like k = (o ∈ (k × k))

instance (Semigroupoid k) => Semigroupoid (Like k) where
  Like f g ∘ Like h i = Like (h ∘ f) (g ∘ i)

type TensoredObjects ::
  forall o (k :: CATEGORY o).
  ((k × k) --> k) ->
  o ->
  (o, o) ->
  (o, o)
type TensoredObjects tensor e ab =
  '( Act tensor '(e, Fst ab),
     Act tensor '(e, Snd ab)
   )

data
  Tensored ::
    forall (k :: CATEGORY o).
    ((k × k) --> k) ->
    CATEGORY (o, o) ->
    CATEGORY (o, o)
  where
  Tensored ::
    !(arr (TensoredObjects tensor e ab) st) ->
    Tensored tensor arr ab st

type instance o ∈ Tensored tensor arr = (o ∈ arr)
