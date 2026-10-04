module Cats.Day
  ( DataDay (..),
    Day,
    bogusLTypes,
    dayToComposeTypes,
    composeToDayTypes,
    Day₁,
  )
where

import Cats.Adjoint
import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.Compose
import Cats.Constructor
import Cats.CrossProduct
import Cats.Delta
import Cats.Exponential
import Cats.Functor
import Cats.Id
import Cats.MonoidObject
import Cats.Monoidal
import Control.Applicative qualified as Prelude
import Data.Function ((&))
import Data.Void qualified as Prelude
import Prelude qualified

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
    forall d c.
    ((d × d) --> d) ->
    (d --> c) ->
    (d --> c) ->
    (d --> c)

type instance Act (Day o f g) z = DataDay o f g z

-- This existential stores representatives of the Day coend. For arbitrary d,
-- it does not identify representatives related by moving a source morphism
-- between the combining arrow and a functor argument. In particular, clients
-- can observe intermediate arrows when d carries more data than functions.
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
dayToComposeTypes = EXP \(type i) (DataDayTypes xyz fx gy) ->
  with @(Acts g i) do
    map f (\x -> map g (\y -> xyz (x, y)) gy) fx

bogusLTypes :: forall x y -> Act f x -> Act g y -> Act (Day @Types @Types (∧) f g) y
bogusLTypes x _ f_ gi = DataDayTypes (\(_ :: x, v) -> v) f_ gi

composeToDayTypes ::
  forall f g r.
  (f ⊣ r, Functor g) =>
  (f • g) ~> Day @Types @Types (∧) f g
composeToDayTypes = EXP \(type i) ->
  acting (type g) (type i) do
    rightToLeft r f \gi ->
      () & leftToRight f r \f_ ->
        bogusLTypes @f @g (type ()) i f_ gi

-- Day as a binary operator on functors
type data Day₁ :: forall d c. BINARY_OP d -> BINARY_OP (c ^ d)

type instance Act (Day₁ o) fg = Day o (Fst fg) (Snd fg)

instance
  (Category d, Functor o) =>
  Functor (Day₁ @d @Types o)
  where
  map _ (l :×: r) = EXP \_ (DataDayTypes @x @y xyz fx gy) ->
    DataDayTypes @x @y xyz ((l $$ x) fx) ((r $$ y) gy)

-- Over Types, parametricity of the hidden object types gives the usual Day
-- encoding for lawful functors. Over a general source category, reassociation
-- can move observable data from an inner arrow to the outer arrow, so the two
-- operations need not be inverses without the coend identifications. Keep
-- construction and mapping generic, but restrict this instance to Types.
instance (Associative o) => Associative (Day₁ @Types @Types o) where
  lassoc _ _ _ _ = EXP \_ (DataDayTypes @x @_ @z xyz fx (DataDayTypes @a @b @_ aby ga hb)) ->
    with @(Acts o '(a, b), Acts o '(x, a)) do
      DataDayTypes @(Act o '(x, a)) @b @z
        (xyz ∘ map o (identity x :×: aby) ∘ rassoc o x a b)
        (DataDayTypes @x @a @(Act o '(x, a)) (identity _) fx ga)
        hb
  rassoc _ _ _ _ = EXP \_ (DataDayTypes @_ @y @z xyz (DataDayTypes @a @b @_ abx fa gb) hy) ->
    with @(Acts o '(a, b), Acts o '(b, y)) do
      DataDayTypes @a @(Act o '(b, y)) @z
        (xyz ∘ map o (abx :×: identity y) ∘ lassoc o a b y)
        fa
        (DataDayTypes @b @y @(Act o '(b, y)) (identity _) gb hy)

type instance MonoidalEmpty (Day₁ (∧)) = Id

instance Monoidal (Day₁ @Types @Types (∧)) where
  idl = EXP \i (DataDayTypes xyz x my :: DataDay (∧) Id m i) -> map m (\y -> xyz (x, y)) my
  coidl = EXP \_ my -> DataDayTypes Prelude.snd () my
  idr = EXP \i (DataDayTypes xyz mx y :: DataDay (∧) m Id i) -> map m (\x -> xyz (x, y)) mx
  coidr = EXP \_ mx -> DataDayTypes Prelude.fst mx ()

instance
  (Prelude.Applicative m) =>
  MonoidObject (Day₁ @Types @Types (∧)) (Constructor m)
  where
  empty _ _ = EXP \_ -> Prelude.pure
  append _ _ = EXP \_ (DataDayTypes xyz mx my) -> Prelude.liftA2 (\x y -> xyz (x, y)) mx my

type Blank = Δ' ()

type instance MonoidalEmpty (Day₁ (∨)) = Blank

instance Monoidal (Day₁ @Types @Types (∨)) where
  idl = EXP \_ (DataDayTypes doxyz () gy :: DataDay (∨) f g z) -> map g (doxyz ∘ Prelude.Right) gy
  coidl = EXP \i (mi :: Act m i) -> DataDayTypes @_ @_ @_ @_ @Blank @m (Prelude.either Prelude.absurd (identity _)) () mi
  idr = EXP \_ (DataDayTypes doxyz fx () :: DataDay (∨) f g z) -> map f (doxyz ∘ Prelude.Left) fx
  coidr = EXP \i (mi :: Act m i) -> DataDayTypes @_ @_ @_ @_ @m @Blank (Prelude.either (identity _) Prelude.absurd) mi ()

instance
  (Prelude.Alternative m) =>
  MonoidObject (Day₁ @Types @Types (∨)) (Constructor m)
  where
  empty _ _ = EXP \_ () -> Prelude.empty
  append _ _ = EXP \_ (DataDayTypes doxyz mx my :: DataDay (∨) f g z) ->
    map f (doxyz ∘ Prelude.Left) mx Prelude.<|> map g (doxyz ∘ Prelude.Right) my
