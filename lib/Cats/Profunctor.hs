module Cats.Profunctor where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Cats.Hom
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

type IsoLike = Glass RTL (Like Types)

type OsiLike = Glass LTR (Like Types)

type ViewLike = Glass RTL (Viewer Types)

type ReviewLike = Glass LTR (Viewer Types)

type instance o ∈ IsoLike = o ∈ Like Types

instance Semigroupoid IsoLike where
  Window abst ∘ Window xyab = Window (abst ∘ xyab)

instance Category IsoLike where
  identity _ = Window (identity _)

type instance o ∈ OsiLike = o ∈ Like Types

instance Semigroupoid OsiLike where
  Mirror xyab ∘ Mirror abst = Mirror (abst ∘ xyab)

instance Category OsiLike where
  identity _ = Mirror (identity _)

type instance o ∈ ViewLike = o ∈ Viewer Types

instance Semigroupoid ViewLike where
  Window xyab ∘ Window abst = Window (xyab ∘ abst)

instance Category ViewLike where
  identity _ = Window (identity _)

type instance o ∈ ReviewLike = o ∈ Viewer Types

instance Semigroupoid ReviewLike where
  Mirror abst ∘ Mirror xyab = Mirror (xyab ∘ abst)

instance Category ReviewLike where
  identity _ = Mirror (identity _)

type data InOptic :: forall d -> (c --> Types) -> d --> Types

type instance Act (InOptic d c) o = Act c o

instance Functor (InOptic IsoLike (Hom (->))) where
  map _ (Window (Like sa bt)) ar = bt ∘ ar ∘ sa

instance Functor (InOptic IsoLike (Cosliced ViewLike xy)) where
  map _ (Window (Like sa _bt)) (Window ar) = Window (Viewer sa ∘ ar)
