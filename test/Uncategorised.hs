module Uncategorised where

import Cats.Adjoint
import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.CrossProduct
import Cats.Curry
import Cats.Functor
import Cats.Monoidal
import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy)
import Data.Type.Equality (type (~))

{- Monoid: definition -}

-- Monoids are categories with a single object
type Monoid :: CATEGORY i -> i -> Constraint
class (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

instance (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

{- Referencing special objects -}

type OBJECT :: forall i. CATEGORY i -> Type
type OBJECT k = Proxy k -> Type

type ObjectName :: OBJECT k -> NamesOf k
type family ObjectName o

type data AnObject :: forall (k :: CATEGORY i) -> NamesOf k -> OBJECT k

type instance ObjectName (AnObject k n) = n

{- Category: 1 -}

data One :: CATEGORY () where
  ONE :: One '() '()

type instance Obj One t = (t ~ '())

instance Semigroupoid One where
  ONE ∘ ONE = ONE

instance Category One where
  identity () = ONE

{- Binary functors: associative, monoidal, braided, symmetric, closed -}

type Braided ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class (Associative p) => Braided (p :: BINARY_OP k) where
  braid :: (x ∈ k, y ∈ k) => k ((x ☼ y) p) ((y ☼ x) p)

type Symmetric ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class (Braided p) => Symmetric p

type BraidedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class
  ( Monoidal p,
    Braided p
  ) =>
  BraidedMonoidal p

type SymmetricMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class
  ( Monoidal p,
    Symmetric p
  ) =>
  SymmetricMonoidal p

type data Twist :: BINARY_OP k -> BINARY_OP k

type instance Act (Twist p) x = Act p '(Snd x, Fst x)

instance (Functor p) => Functor (Twist p) where
  map _ (r :×: l) = map p (l :×: r)

type With₁ p = Curry₂ p

type With₂ p = Curry₂ (Twist p)

type ClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  Constraint
class
  ( forall y. (y ∈ k) => With₂ p y ⊣ With₁ e y,
    Monoidal p
  ) =>
  ClosedMonoidal p (e :: BINARY_OP k)
    | p -> e,
      e -> p

type SymmetricClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  Constraint
class
  ( SymmetricMonoidal p,
    ClosedMonoidal p e
  ) =>
  SymmetricClosedMonoidal p e
    | p -> e,
      e -> p

{- Tensory objects -}

{- coyoneda -}

data DataCoyoneda :: forall k. (k --> Types) -> NamesOf k -> Type where
  MakeDataCoyoneda :: (a ∈ k) => Act f a -> k a b -> DataCoyoneda @k f b

type data Coyoneda :: (k --> Types) -> (k --> Types)

type instance Act (Coyoneda f) x = DataCoyoneda f x

instance (Category k) => Functor (Coyoneda @k f) where
  map _ ab (MakeDataCoyoneda fx xa) = MakeDataCoyoneda fx (ab ∘ xa)

-- Natural numbers
data N = S N | Z

-- "Less than or equal to for Natural numbers" forms a category
data (≤) :: CATEGORY N where
  E :: n ≤ n
  B :: l ≤ u -> l ≤ 'S u

type CanonicalN :: N -> N
type family CanonicalN n where
  CanonicalN 'Z = 'Z
  CanonicalN ('S k) = 'S (CanonicalN k)

type instance Obj (≤) x = x ~ CanonicalN x

instance Semigroupoid (≤) where
  E ∘ r = r
  B l ∘ r = B (l ∘ r)

instance Category (≤) where
  identity _ = E
