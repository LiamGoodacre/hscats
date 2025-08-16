module Cats.Profunctor where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Data.Kind (Constraint)
import Data.Type.Equality (type (~))

newtype Viewer :: CATEGORY o -> CATEGORY (o, o) where
  Viewer :: {runViewer :: arr (Fst st) (Fst ab)} -> Viewer arr ab st

type instance o ∈ Viewer arr = o ∈ (arr × arr)

instance (Semigroupoid arr) => Semigroupoid (Viewer arr) where
  Viewer f ∘ Viewer g = Viewer (g ∘ f)

instance (Category arr) => Category (Viewer arr) where
  identity _ = Viewer (identity _)

data Like :: CATEGORY o -> CATEGORY (o, o) where
  Like ::
    !(arr (Fst st) (Fst ab)) ->
    !(arr (Snd ab) (Snd st)) ->
    Like arr ab st

type instance o ∈ Like arr = o ∈ (arr × arr)

instance (Semigroupoid arr) => Semigroupoid (Like arr) where
  Like f g ∘ Like h i = Like (h ∘ f) (g ∘ i)

instance (Category arr) => Category (Like arr) where
  identity _ = Like (identity _) (identity _)

type TensoredObjects ::
  forall o (arr :: CATEGORY o).
  ((arr × arr) --> arr) ->
  o ->
  (o, o) ->
  (o, o)
type TensoredObjects tensor e ab =
  '( Act tensor '(e, Fst ab),
     Act tensor '(e, Snd ab)
   )

data
  Tensored ::
    forall (arr :: CATEGORY o).
    ((arr × arr) --> arr) ->
    CATEGORY (o, o) ->
    CATEGORY (o, o)
  where
  Tensored ::
    !(arr (TensoredObjects tensor e ab) st) ->
    Tensored tensor arr ab st

type instance o ∈ Tensored tensor arr = o ∈ arr

type data Direction = RTL | LTR

type ReverseDirection :: Direction -> Direction
type family ReverseDirection dir where
  ReverseDirection RTL = LTR
  ReverseDirection LTR = RTL

data Glass :: Direction -> CATEGORY (o, o) -> CATEGORY (o, o) where
  Window :: !(proarr '(a, b) '(s, t)) -> Glass RTL proarr '(a, b) '(s, t)
  Mirror :: !(proarr '(t, s) '(b, a)) -> Glass LTR proarr '(a, b) '(s, t)

type Reversible :: CATEGORY (o, o) -> CATEGORY (o, o) -> Constraint
class Reversible input output | input -> output, output -> input where
  reversed :: input '(a, b) '(s, t) -> output '(t, s) '(b, a)

instance Reversible (Like arr) (Like arr) where
  reversed (Like sa bt) = Like bt sa

instance
  (m ~ ReverseDirection w, ReverseDirection m ~ w) =>
  Reversible (Glass m arr) (Glass w arr)
  where
  reversed (Window k) = Mirror k
  reversed (Mirror k) = Window k
