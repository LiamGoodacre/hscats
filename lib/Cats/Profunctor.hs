module Cats.Profunctor where

import Cats.Category
import Cats.CrossProduct
import Cats.Functor
import Cats.Opposite
import Data.Kind (Type)

-- import Data.Type.Equality (type (~))

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

data
  DataProcompose ::
    PROFUNCTOR a b ->
    PROFUNCTOR x a ->
    NamesOf x ->
    NamesOf b ->
    Type
  where
  MkProcompose ::
    forall
      {s}
      {t}
      {u}
      {a :: CATEGORY s}
      {b :: CATEGORY t}
      {x :: CATEGORY u}
      (m :: NamesOf a)
      (i :: NamesOf x)
      (j :: NamesOf b)
      (p :: PROFUNCTOR a b)
      (q :: PROFUNCTOR x a).
    ( m ∈ a,
      i ∈ x,
      j ∈ b
    ) =>
    Act p '(m, j) ->
    Act q '(i, m) ->
    DataProcompose p q i j

data Procompose :: PROFUNCTOR a b -> PROFUNCTOR x a -> PROFUNCTOR x b

type instance Act (Procompose p q) '(i, j) = DataProcompose p q i j

-- instance
--   (Category b, Category x, Profunctor p, Profunctor q) =>
--   Functor (Procompose (p :: PROFUNCTOR a b) (q :: PROFUNCTOR x a) :: PROFUNCTOR x b)
--   where
--   map ::
--     forall (f' :: (Op x × b) --> Types) ->
--     ( f' ~ (Procompose p q),
--       ii ∈ (Op x × b),
--       jj ∈ (Op x × b)
--     ) =>
--     (Op x × b) ii jj ->
--     Types
--       (Act (Procompose p q) ii)
--       (Act (Procompose p q) jj)
--   map _ (OP l :×: r :: (Op x × b) ii jj) (MkProcompose @m pp qq) =
--     acting (type p) (type '(m, Snd ii)) do
--       MkProcompose @m
--         (rmap (type p) r pp)
--         (lmap (type q) l qq)
