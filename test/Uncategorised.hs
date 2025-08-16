module Uncategorised where

import Cats.Adjoint
import Cats.Associative
import Cats.Binary
import Cats.Category
import Cats.Compose
import Cats.CrossProduct
import Cats.Curry
import Cats.Exponential
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

{- Functor: eval/curry -}

type data Eval :: forall d c. ((c ^ d) × d) --> c

type instance Act Eval fx = Act (Fst fx) (Snd fx)

type instance Super Functor Eval = ()

instance
  (Category d, Category c) =>
  Functor (Eval @d @c)
  where
  map @a @b _ (f :×: x) = map (Fst b) x ∘ (f $$ Snd a)

{- Monad & Comonad -}

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

type MonadBy :: (c --> c) -> CATEGORY i -> Constraint
type MonadBy m d =
  ( m ~ TheCompositionBy m d,
    InnerBy m d ⊣ OuterBy m d
  )

type Monad :: (c --> c) -> Constraint
type Monad m = MonadBy m (MidComposition m)

type ComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type ComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d
  )

type Comonad :: (c --> c) -> Constraint
type Comonad w = ComonadBy w (MidComposition w)

type Invert :: forall c. forall (m :: c --> c) -> (MidComposition m --> MidComposition m)
type Invert m = Inner m • Outer m

flatMap ::
  forall {c} a b {f} {g}.
  forall (m :: c --> c) ->
  (m ~ (g • f), f ⊣ g, a ∈ c, b ∈ c) =>
  c a (Act m b) ->
  c (Act m a) (Act m b)
flatMap m amb = join m b ∘ map m amb

{- Category: 1 -}

data One :: CATEGORY () where
  ONE :: One '() '()

type instance t ∈ One = (t ~ '())

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
  i ->
  Constraint
class
  ( Monoidal p id,
    Braided p
  ) =>
  BraidedMonoidal p id
    | p -> id

type SymmetricMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  Constraint
class
  ( Monoidal p id,
    Symmetric p
  ) =>
  SymmetricMonoidal p id
    | p -> id

type data Twist :: BINARY_OP k -> BINARY_OP k

type instance Act (Twist p) x = Act p '(Snd x, Fst x)

type instance Super Functor (Twist p) = ()

instance (Functor p) => Functor (Twist p) where
  map _ (r :×: l) = map p (l :×: r)

type With₁ p = Curry₂ p

type With₂ p = Curry₂ (Twist p)

type ClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  i ->
  Constraint
class
  ( forall y. (y ∈ k) => With₂ p y ⊣ With₁ e y,
    Monoidal p id
  ) =>
  ClosedMonoidal p (e :: BINARY_OP k) id
    | p -> e id,
      e -> p id

type SymmetricClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  i ->
  Constraint
class
  ( SymmetricMonoidal p id,
    ClosedMonoidal p e id
  ) =>
  SymmetricClosedMonoidal p e id
    | p -> e id,
      e -> p id

{- Tensory objects -}

{- coyoneda -}

data DataCoyoneda :: forall k. (k --> Types) -> NamesOf k -> Type where
  MakeDataCoyoneda :: (a ∈ k) => Act f a -> k a b -> DataCoyoneda @k f b

type data Coyoneda :: (k --> Types) -> (k --> Types)

type instance Act (Coyoneda f) x = DataCoyoneda f x

type instance Super Functor (Coyoneda f) = ()

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

type instance x ∈ (≤) = x ~ CanonicalN x

instance Semigroupoid (≤) where
  E ∘ r = r
  B l ∘ r = B (l ∘ r)

instance Category (≤) where
  identity _ = E
