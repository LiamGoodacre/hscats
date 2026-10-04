module Cats.FromAdjoint
  ( AdjunctionMonad,
    AdjunctionMonadBy,
    AdjunctionComonad,
    AdjunctionComonadBy,
    TheComposition,
    Invert,
  )
where

import Cats.Adjoint
import Cats.Category
import Cats.Compose
import Cats.Functor
import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (~))

{- AdjunctionMonad & AdjunctionComonad -}

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

type AdjunctionMonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionMonadBy m d =
  ( m ~ TheCompositionBy m d,
    InnerBy m d ⊣ OuterBy m d
  )

type AdjunctionMonad :: (c --> c) -> Constraint
type AdjunctionMonad m = AdjunctionMonadBy m (MidComposition m)

type AdjunctionComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type AdjunctionComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d
  )

type AdjunctionComonad :: (c --> c) -> Constraint
type AdjunctionComonad w = AdjunctionComonadBy w (MidComposition w)

type Invert :: forall c. forall (m :: c --> c) -> (MidComposition m --> MidComposition m)
type Invert m = Inner m • Outer m
