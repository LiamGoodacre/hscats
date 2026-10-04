module Cats.Procompose where

import Cats.Category
import Cats.Functor
import Cats.Profunctor
import Data.Kind (Type)

-- import Data.Type.Equality (type (~))

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
