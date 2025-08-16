module Cats.Compose where

import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor

type data (•) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f • g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f • g) where
  map _ = map f ∘ map g

above ::
  forall k f g.
  (Functor k) =>
  (f ~> g) ->
  ((f • k) ~> (g • k))
above fg = EXP \i -> fg $$ Act k i

beneath ::
  forall k f g.
  (Functor k, Functor f, Functor g) =>
  (f ~> g) ->
  ((k • f) ~> (k • g))
beneath fg = EXP \i -> map k (fg $$ i)

-- Functor in the two functors arguments
-- `(f • g) v` is a functor in `f`, and `g`
type data Composing :: forall a b x. ((b ^ a) × (a ^ x)) --> (b ^ x)

type instance Act Composing e = Fst e • Snd e

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composing @aa @bb @cc)
  where
  map _ ((fh :: f ~> h) :×: (gi :: g ~> i)) =
    beneath gi ∘ above fh :: (f • g) ~> (h • i)

-- `(f • g) v` is a functor in `f`, `g`, and `v`
type data Composed :: forall a b c. (((b ^ a) × (a ^ c)) × c) --> b

type instance Act Composed e = Act (Act Composing (Fst e)) (Snd e)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composed @aa @bb @cc)
  where
  map _ (fhgi :×: (xy :: cc x y)) =
    case map (Composing @aa @bb @cc) fhgi of
      (v :: (f • g) ~> (h • i)) ->
        map (h • i) xy ∘ (v $$ x)
