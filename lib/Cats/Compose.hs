module Cats.Compose where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.Id
import Cats.Monoidal

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
