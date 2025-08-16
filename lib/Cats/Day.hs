module Cats.Day
  ( DataDay (..),
    Day,
    bogusLTypes,
    dayToComposeTypes,
    composeToDayTypes,
  )
where

import Cats.Adjoint
import Cats.Category
import Cats.Compose
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.Product
import Data.Function ((&))
import GHC.Tuple (Unit)

type DataDay ::
  forall d c.
  ((d × d) --> d) ->
  (d --> c) ->
  (d --> c) ->
  NamesOf d ->
  NamesOf c
data family DataDay o f g z

type data
  Day ::
    ((d × d) --> d) ->
    (d --> c) ->
    (d --> c) ->
    (d --> c)

type instance Act (Day o f g) z = DataDay o f g z

data instance DataDay @d @Types o f g z where
  DataDayTypes ::
    forall {d} x y z o f g.
    (x ∈ d, y ∈ d, z ∈ d) =>
    d (Act o '(x, y)) z ->
    Act f x ->
    Act g y ->
    DataDay @d @Types o f g z

instance
  (Category d, Functor o) =>
  Functor (Day @d @Types o f g)
  where
  map _ dab (DataDayTypes @x @y xyz fx gy) =
    DataDayTypes @x @y (dab ∘ xyz) fx gy

dayToComposeTypes ::
  forall f g.
  (Functor f, Functor g) =>
  Day (∧) f g ~> (f • g)
dayToComposeTypes = EXP \_ (DataDayTypes xyz fx gy) ->
  map f (\x -> map g (\y -> xyz (x, y)) gy) fx

bogusLTypes :: forall x y -> Act f x -> Act g y -> Act (Day @Types @Types (∧) f g) y
bogusLTypes x _ f_ gi = DataDayTypes (\(_ :: x, v) -> v) f_ gi

composeToDayTypes ::
  forall f g r.
  (f ⊣ r, Functor g) =>
  (f • g) ~> Day @Types @Types (∧) f g
composeToDayTypes = EXP \i ->
  rightToLeft r f \gi ->
    () & leftToRight f r \f_ ->
      bogusLTypes @f @g Unit i f_ gi
