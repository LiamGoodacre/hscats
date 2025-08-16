module Cats.Day where

import Cats.Category
import Cats.Functor
import Cats.Product

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
