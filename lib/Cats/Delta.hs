module Cats.Delta where

import Cats.Adjoint
import Cats.Associative
import Cats.Category
import Cats.CrossProduct
import Cats.Exponential
import Cats.Functor
import Cats.MonoidObject
import Cats.Monoidal
import Cats.Opposite
import Data.Void (Void)
import Data.Void qualified as Void
import Prelude qualified

-- (∨) ⊣ Δ₂ Types ⊣ (∧)

type data Δ₂ :: forall (k :: CATEGORY i) -> (k --> (k × k))

type instance Act (Δ₂ k) x = '(x, x)

instance (Category k) => Functor (Δ₂ k) where
  map _ f = f :×: f

type data (∧) :: (Types × Types) --> Types

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map _ (f :×: g) (a, b) = (f a, g b)

type data (∨) :: (Types × Types) --> Types

type instance Act (∨) x = Prelude.Either (Fst x) (Snd x)

instance Functor (∨) where
  map _ (f :×: g) = Prelude.either (Prelude.Left ∘ f) (Prelude.Right ∘ g)

instance Δ₂ Types ⊣ (∧) where
  rightToLeft _ _ t = (Prelude.fst ∘ t) :×: (Prelude.snd ∘ t)
  leftToRight _ _ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ₂ Types where
  rightToLeft _ _ (f :×: g) = f `Prelude.either` g
  leftToRight _ _ t = (t ∘ Prelude.Left) :×: (t ∘ Prelude.Right)

instance Associative (∧) where
  lassoc _ _ _ _ = \(a, (b, c)) -> ((a, b), c)
  rassoc _ _ _ _ = \((a, b), c) -> (a, (b, c))

instance Associative (∨) where
  lassoc _ _ _ _ = \case
    Prelude.Left a -> Prelude.Left (Prelude.Left a)
    Prelude.Right (Prelude.Left b) -> Prelude.Left (Prelude.Right b)
    Prelude.Right (Prelude.Right c) -> Prelude.Right c
  rassoc _ _ _ _ = \case
    Prelude.Left (Prelude.Left a) -> Prelude.Left a
    Prelude.Left (Prelude.Right b) -> Prelude.Right (Prelude.Left b)
    Prelude.Right c -> Prelude.Right (Prelude.Right c)

type instance MonoidalEmpty (∧) = ()

instance Monoidal (∧) where
  idl = \(_, m) -> m
  coidl = \m -> ((), m)
  idr = \(m, _) -> m
  coidr = \m -> (m, ())

type instance MonoidalEmpty (∨) = Void

instance Monoidal (∨) where
  idl = Prelude.either Void.absurd Prelude.id
  coidl = Prelude.Right
  idr = Prelude.either Prelude.id Void.absurd
  coidr = Prelude.Left

instance
  (Prelude.Monoid m) =>
  MonoidObject (∧) m
  where
  empty _ _ = \() -> Prelude.mempty
  append _ _ = \(l, r) -> Prelude.mappend l r

-- Every object of Types has the cartesian comonoid: discard and copy.
instance MonoidObject (OpTensor (∧)) m where
  empty _ _ = OP (\_ -> ())
  append _ _ = OP (\m -> (m, m))

mempty :: (MonoidObject (∧) m) => m
mempty = empty (type (∧)) (type _) ()

(<>) :: (MonoidObject (∧) m) => m -> m -> m
l <> r = append (type (∧)) (type _) (l, r)

-- ∃ ⊣ Δ @Types ⊣ ∀

type data Δ' :: NamesOf k -> x --> k

type instance Act (Δ' a) b = a

instance (Category k, Category x, a ∈ k) => Functor (Δ' @k @x a) where
  map _ _ = identity _

type data Δ :: k --> (k ^ x)

type instance Act (Δ @k) a = Δ' @k a

instance (Category k, Category x) => Functor (Δ @k @x) where
  map _ ab = EXP \_ -> ab

type data Exists :: forall d c. (c ^ d) --> c

data family DataExists (f :: d --> c)

data instance DataExists (f :: d --> Types) where
  DataExistsTypes :: forall {d} i (f :: d --> Types). (i ∈ d) => Act f i -> DataExists f

type instance Act (Exists @d @c) f = DataExists f

instance (Category d) => Functor (Exists @d @Types) where
  map _ (t :: f ~> g) (DataExistsTypes @i (fi :: Act f i)) = DataExistsTypes @i ((t $$ i) fi)

type data Forall :: forall d c. (c ^ d) --> c

data family DataForall (f :: d --> c)

data instance DataForall (f :: d --> Types) where
  DataForallTypes :: forall {d} (f :: d --> Types). {runForallTypes :: forall i -> (i ∈ d) => Act f i} -> DataForall f

type instance Act (Forall @d @c) f = DataForall f

instance (Category d) => Functor (Forall @d @Types) where
  map _ t (DataForallTypes ifi) = DataForallTypes \(type i) -> (t $$ i) (ifi i)

instance Exists @Types ⊣ Δ @Types where
  rightToLeft _ _ a_deltab (DataExistsTypes @a fa) = (a_deltab $$ a) fa
  leftToRight _ _ existsa_b = EXP \i ai -> existsa_b (DataExistsTypes @i ai)

instance Δ @Types ⊣ Forall @Types where
  rightToLeft _ _ a_forallb = EXP \i a -> runForallTypes (a_forallb a) i
  leftToRight _ _ deltaa_b a = DataForallTypes \i -> (deltaa_b $$ i) a
