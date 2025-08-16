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
import Data.Function ((&))
import GHC.Tuple (Unit)
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
dayToComposeTypes = EXP \_ (DataDayTypes xyz fx gy) ->
  map f (\x -> map g (\y -> xyz (x, y)) gy) fx

bogusLTypes :: forall x y -> Act f x -> Act g y -> Act (Day @Types @Types (∧) f g) y
bogusLTypes x _ f_ gi = DataDayTypes (\(_ :: x, v) -> v) f_ gi

composeToDayTypes ::
  forall f g r.
  (f ⊣ r, Functor g) =>
  (f • g) ~> Day @Types @Types (∧) f g
composeToDayTypes = EXP \i ->
  rightToLeft r f \gi ->
    () & leftToRight f r \f_ ->
      bogusLTypes @f @g Unit i f_ gi

type data
  Day₁ ::
    forall d c.
    ((d × d) --> d) ->
    ((c ^ d) × (c ^ d)) --> (c ^ d)

type instance Act (Day₁ o) fg = Day o (Fst fg) (Snd fg)

instance
  (Category d, Functor o) =>
  Functor (Day₁ @d @Types o)
  where
  map _ (l :×: r) = EXP \_ (DataDayTypes @x @y xyz fx gy) ->
    DataDayTypes @x @y xyz ((l $$ x) fx) ((r $$ y) gy)

instance (Associative o) => Associative (Day₁ @d @Types o) where
  lassoc _ _ _ _ = EXP \_ (DataDayTypes @x @_ @z xyz fx (DataDayTypes @a @b @_ aby ga hb)) ->
    DataDayTypes @(Act o '(x, a)) @b @z
      (xyz ∘ map o (identity x :×: aby) ∘ rassoc o x a b)
      (DataDayTypes @x @a @(Act o '(x, a)) (identity _) fx ga)
      hb
  rassoc _ _ _ _ = EXP \_ (DataDayTypes @_ @y @z xyz (DataDayTypes @a @b @_ abx fa gb) hy) ->
    DataDayTypes @a @(Act o '(b, y)) @z
      (xyz ∘ map o (abx :×: identity y) ∘ lassoc o a b y)
      fa
      (DataDayTypes @b @y @(Act o '(b, y)) (identity _) gb hy)

instance Monoidal (Day₁ (∧)) Id where
  idl = EXP \i (DataDayTypes xyz x my :: DataDay (∧) Id m i) -> map m (\y -> xyz (x, y)) my
  coidl = EXP \_ my -> DataDayTypes (\((), v) -> v) () my
  idr = EXP \i (DataDayTypes xyz mx y :: DataDay (∧) m Id i) -> map m (\x -> xyz (x, y)) mx
  coidr = EXP \_ mx -> DataDayTypes (\(v, ()) -> v) mx ()

instance
  (Prelude.Applicative m) =>
  MonoidObject (Day₁ @Types @Types (∧)) Id (Constructor m)
  where
  empty_ = EXP \_ -> Prelude.pure
  append_ = EXP \_ (DataDayTypes xyz mx my) -> Prelude.liftA2 (\x y -> xyz (x, y)) mx my
