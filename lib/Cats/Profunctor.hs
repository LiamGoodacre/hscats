module Cats.Profunctor where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Cats.Opposite

infixr 0 -/->

type PROFUNCTOR d c = (Op d × c) --> Types

type c -/-> d = PROFUNCTOR d c

class (Functor p) => Profunctor (p :: PROFUNCTOR d c)

instance (Functor p) => Profunctor (p :: PROFUNCTOR d c)

lmap ::
  forall {d} {c} {x} {i} {o}.
  forall (p :: PROFUNCTOR d c) ->
  (Functor p, Category c, x ∈ c, i ∈ d, o ∈ d) =>
  d i o ->
  Act p '(o, x) ->
  Act p '(i, x)
lmap (type p) dio = map (type p) (OP dio :×: identity (type x))

rmap ::
  forall {d} {c} {x} {i} {o}.
  forall (p :: PROFUNCTOR d c) ->
  (Functor p, Category d, x ∈ d, i ∈ c, o ∈ c) =>
  c i o ->
  Act p '(x, i) ->
  Act p '(x, o)
rmap (type p) cio = map (type p) (identity (type x) :×: cio)

dimap ::
  forall {d} {c} {a} {b} {s} {t}.
  forall (p :: PROFUNCTOR d c) ->
  (Functor p, Category d, s ∈ d, a ∈ d, b ∈ c, t ∈ c) =>
  d s a ->
  c b t ->
  Act p '(a, b) ->
  Act p '(s, t)
dimap (type p) dsa cbt = map (type p) (OP dsa :×: cbt)
