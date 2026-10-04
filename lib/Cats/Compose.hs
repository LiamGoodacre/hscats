module Cats.Compose where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.Id
import Cats.Monoidal
import Cats.Profunctor
import Data.Kind (Type)

-- import Data.Type.Equality (type (~))

type data (•) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f • g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f • g) where
  map _ = map (type f) ∘ map (type g)

above ::
  forall k f g.
  (Functor k) =>
  (f ~> g) ->
  ((f • k) ~> (g • k))
above fg = EXP \(type i) -> fg $$ Act k i

beneath ::
  forall k f g.
  (Functor k, Functor f, Functor g) =>
  (f ~> g) ->
  ((k • f) ~> (k • g))
beneath fg = EXP \(type i) ->
  with @(Acts f i, Acts g i) do
    map (type k) (fg $$ i)

-- Functor in the two functors arguments
-- `(f • g) v` is a functor in `f`, and `g`
type data Composing :: forall a b x. ((b ^ a) × (a ^ x)) --> (b ^ x)

type instance Act Composing e = Fst e • Snd e

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composing @aa @bb @cc)
  where
  map _ ((fh :: f ~> h) :×: (gi :: g ~> i)) =
    with @(h ∈ (bb ^ aa), g ∈ (aa ^ cc), i ∈ (aa ^ cc)) do
      beneath gi ∘ above fh :: (f • g) ~> (h • i)

instance (Category k) => Associative (Composing :: BINARY_OP (k ^ k)) where
  lassoc _ (type f) (type g) (type h) =
    EXP \(type i) -> identity (f • (g • h)) $$ i
  rassoc _ (type f) (type g) (type h) =
    EXP \(type i) -> identity ((f • g) • h) $$ i

type instance MonoidalEmpty Composing = Id

instance
  (Category k) =>
  Monoidal (Composing :: BINARY_OP (k ^ k))
  where
  idl = EXP \_ -> identity _
  coidl = EXP \_ -> identity _
  idr = EXP \_ -> identity _
  coidr = EXP \_ -> identity _

-- `(f • g) v` is a functor in `f`, `g`, and `v`
type data Composed :: forall a b c. (((b ^ a) × (a ^ c)) × c) --> b

type instance Act Composed e = Act (Act Composing (Fst e)) (Snd e)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composed @aa @bb @cc)
  where
  map _ ((fhgi :: p fg hi) :×: (xy :: cc x y)) =
    with @(hi ∈ p) do
      case map (Composing @aa @bb @cc) fhgi of
        (v :: (f • g) ~> (h • i)) ->
          map (h • i) xy ∘ (v $$ x)

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
