module Cats.Compose where

import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.Id
import Cats.Monoidal
import Data.Kind (Type)

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

-- instance
--   ( Monad m,
--     m ~ (f • g)
--   ) =>
--   MonoidObject (Composing :: BINARY_OP (k ^ k)) (m :: k --> k)
--   where
--   empty _ _ = EXP \_ -> unit m _
--   append _ _ = EXP \(type a) -> join m a

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

{- Decomposition -}

type MidCompositionIx :: forall c. (c --> c) -> Type
type family MidCompositionIx m where
  MidCompositionIx (g • f) = NamesOf (DomainOf g)

type MidComposition :: forall c. forall (m :: c --> c) -> CATEGORY (MidCompositionIx m)
type family MidComposition m where
  MidComposition (g • f) = DomainOf g

type OuterBy :: (c --> c) -> forall (d :: CATEGORY i) -> (d --> c)
type family OuterBy m d where
  OuterBy (g • f) d = g

type InnerBy :: (c --> c) -> forall (d :: CATEGORY i) -> (c --> d)
type family InnerBy m d where
  InnerBy (g • f) d = f

type Inner :: forall (m :: c --> c) -> (c --> MidComposition m)
type Inner m = InnerBy m (MidComposition m)

type Outer :: forall (m :: c --> c) -> (MidComposition m --> c)
type Outer m = OuterBy m (MidComposition m)

type TheCompositionBy :: (c --> c) -> CATEGORY i -> (c --> c)
type TheCompositionBy m d = OuterBy m d • InnerBy m d

type TheComposition :: (c --> c) -> (c --> c)
type TheComposition m = TheCompositionBy m (MidComposition m)
