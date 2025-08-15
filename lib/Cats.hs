module Cats
  ( module Cats.Category,
    module Cats.Category.Op,
    module Cats.Category.Product,
    module Cats.Functor,
    module Cats.Adjoint,
    module Cats,
  )
where

import Cats.Adjoint
import Cats.Category
import Cats.Category.Op
import Cats.Category.Product
import Cats.Functor
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

data AnObject :: forall (k :: CATEGORY i) -> NamesOf k -> OBJECT k

type instance ObjectName (AnObject k n) = n

{- Category: exponentials -}

data (^) :: forall c d -> CATEGORY (d --> c) where
  EXP ::
    { ($$) ::
        forall (i :: NamesOf d) ->
        (i ∈ d) =>
        c (Act f i) (Act g i)
    } ->
    (c ^ d) f g

type (~>) (f :: d --> c) g = (c ^ d) f g

type instance o ∈ (c ^ d) = Functor o

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = EXP \i -> (l $$ i) ∘ (r $$ i)

instance (Category d, Category c) => Category (c ^ d) where
  identity f = EXP \i -> identity (Act f i)

{- Functor: composition as a functor -}

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
data Compose :: forall a b x. ((b ^ a) × (a ^ x)) --> (b ^ x)

-- `(f • g) v` is a functor in `f`, `g`, and `v`
data Composed :: forall a b c. (((b ^ a) × (a ^ c)) × c) --> b

type instance Act Compose e = Fst e • Snd e

type instance Act Composed e = Act (Act Compose (Fst e)) (Snd e)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Compose @aa @bb @cc)
  where
  map _ ((fh :: f ~> h) :×: (gi :: g ~> i)) =
    beneath gi ∘ above fh :: (f • g) ~> (h • i)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composed @aa @bb @cc)
  where
  map _ (fhgi :×: (xy :: cc x y)) =
    case map (Compose @aa @bb) fhgi of
      (v :: (f • g) ~> (h • i)) ->
        map (h • i) xy ∘ (v $$ x)

{- Functor: eval/curry -}

data Eval :: forall d c. ((c ^ d) × d) --> c

-- Typing '²': `^q 2 S`
data Curry² :: forall a b c. ((a × b) --> c) -> NamesOf a -> (b --> c)

-- Typing '¹': `^q 1 S`
data Curry¹ :: forall a b c. ((a × b) --> c) -> (a --> (c ^ b))

-- Typing '⁰': `^q 0 S`
data Curry⁰ :: forall a b c. (c ^ (a × b)) --> ((c ^ b) ^ a)

type instance Act Eval fx = Act (Fst fx) (Snd fx)

type instance Act (Curry² f x) y = Act f '(x, y)

type instance Act (Curry¹ f) x = Curry² f x

type instance Act Curry⁰ f = Curry¹ f

instance
  (Category d, Category c) =>
  Functor (Eval @d @c)
  where
  map @a @b _ (f :×: x) = map (Fst b) x ∘ (f $$ Snd a)

instance
  (Category a, Category b, Functor f, x ∈ a) =>
  Functor (Curry² @a @b f x)
  where
  map _ byz = map f (identity x :×: byz)

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry¹ @a @b @c f)
  where
  map _ axy = EXP \i ->
    map f (axy :×: identity i)

instance
  (Category a, Category b, Category c) =>
  Functor (Curry⁰ @a @b @c)
  where
  map _ (EXP t) = EXP \i -> EXP \j -> t (i, j)

{- Spin -}

type BI d c k = (d × c) --> k

data Spin :: BI d c k -> BI c d k

type instance Act (Spin b) x = Act b '(Snd x, Fst x)

instance
  (Category d, Category c, Functor b) =>
  Functor (Spin (b :: BI d c k))
  where
  map _ (l :×: r) = map b (r :×: l)

{- Hom Functors -}

data Hom :: forall c -> Op c × c --> Types

type instance Act (Hom c) o = c (Fst o) (Snd o)

instance (Category c) => Functor (Hom c) where
  map _ (OP f :×: g) t = g ∘ t ∘ f

-- Typing '⁰': `^q 0 S`
type Hom⁰ :: forall (c :: CATEGORY o) -> c --> (Types ^ Op c)
type Hom⁰ c = Curry¹ (Spin (Hom c))

-- Typing '₀': `^q 0 s`
type Hom₀ :: forall (c :: CATEGORY o) -> Op c --> (Types ^ c)
type Hom₀ c = Curry¹ (Hom c)

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
    InnerBy m d ⊣ OuterBy m d,
    Functor m
  )

type Monad :: (c --> c) -> Constraint
type Monad m = MonadBy m (MidComposition m)

type ComonadBy :: (c --> c) -> CATEGORY i -> Constraint
type ComonadBy w d =
  ( w ~ TheCompositionBy w d,
    OuterBy w d ⊣ InnerBy w d,
    Functor w
  )

type Comonad :: (c --> c) -> Constraint
type Comonad w = ComonadBy w (MidComposition w)

type Invert :: forall c. forall (m :: c --> c) -> (MidComposition m --> MidComposition m)
type Invert m = Inner m • Outer m

unit :: forall (m :: c --> c) a -> (MonadBy m d, a ∈ c) => c a (Act m a)
unit m a = rightAdjoint (Inner m) (Outer m) (identity (Act (Inner m) a))

counit :: forall (w :: d --> d) a -> (ComonadBy w c, a ∈ d) => d (Act w a) a
counit w a = leftAdjoint (Inner w) (Outer w) (identity (Act (Inner w) a))

join ::
  forall (m :: c --> c) a ->
  (m ~ (g • f), f ⊣ g, a ∈ c) =>
  c (Act (m • m) a) (Act m a)
join m a = map (Outer m) (counit (Invert m) (Act (Inner m) a))

extend ::
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act w a) (Act (w • w) a)
extend w a = map (Outer w) (unit (Invert w) (Act (Inner w) a))

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

type BINARY_OP c = BI c c c

type (☼) ::
  forall {i}.
  forall (k :: CATEGORY i).
  i ->
  i ->
  BINARY_OP k ->
  i
type (☼) l r p = Act p '(l, r)

type Associative ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  Constraint
class (Functor op) => Associative (op :: BINARY_OP k) where
  lassoc ::
    forall op' a b c ->
    (op' ~ op) =>
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      ((a ☼ (b ☼ c) op) op)
      (((a ☼ b) op ☼ c) op)
  rassoc ::
    forall op' a b c ->
    (op' ~ op) =>
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      (((a ☼ b) op ☼ c) op)
      ((a ☼ (b ☼ c) op) op)

instance (Category k) => Associative (Compose :: BINARY_OP (k ^ k)) where
  lassoc _ _ _ _ = EXP \_ -> identity _
  rassoc _ _ _ _ = EXP \_ -> identity _

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

type Monoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  Constraint
class
  (Associative p) =>
  Monoidal (p :: BINARY_OP k) id
    | p -> id
  where
  idl :: (m ∈ k) => k ((id ☼ m) p) m
  coidl :: (m ∈ k) => k m ((id ☼ m) p)
  idr :: (m ∈ k) => k ((m ☼ id) p) m
  coidr :: (m ∈ k) => k m ((m ☼ id) p)

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

data Twist :: BINARY_OP k -> BINARY_OP k

type instance Act (Twist p) x = Act p '(Snd x, Fst x)

instance (Functor p) => Functor (Twist p) where
  map _ (r :×: l) = map p (l :×: r)

type With¹ p = Curry² p

type With² p = Curry² (Twist p)

type ClosedMonoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  BINARY_OP k ->
  i ->
  Constraint
class
  ( forall y. (y ∈ k) => With² p y ⊣ With¹ e y,
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

type MonoidObject ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  i ->
  Constraint
class
  ( Monoidal p id,
    m ∈ k
  ) =>
  MonoidObject (p :: BINARY_OP k) id m
    | p -> id
  where
  empty_ :: k id m
  append_ :: k ((m ☼ m) p) m

empty ::
  forall {i} {k :: CATEGORY i} (p :: BINARY_OP k) {id :: i} (m :: i).
  (MonoidObject p id m) =>
  k id m
empty = empty_ @k @p @id @m

append ::
  forall {i} {k :: CATEGORY i} (p :: BINARY_OP k) {id :: i} (m :: i).
  (MonoidObject p id m) =>
  k ((☼) m m p) m
append = append_ @k @p @id @m

instance
  (Category k) =>
  Monoidal Compose (Id :: k --> k)
  where
  idl = EXP \_ -> identity _
  coidl = EXP \_ -> identity _
  idr = EXP \_ -> identity _
  coidr = EXP \_ -> identity _

instance
  ( Monad m,
    m ~ (f • g)
  ) =>
  MonoidObject Compose Id m
  where
  empty_ = EXP \_ -> unit m _
  append_ = EXP \i -> join m i

{- coyoneda -}

data DataCoyoneda :: forall k. (k --> Types) -> NamesOf k -> Type where
  MakeDataCoyoneda :: (a ∈ k) => Act f a -> k a b -> DataCoyoneda @k f b

data Coyoneda :: (k --> Types) -> (k --> Types)

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

type instance x ∈ (≤) = x ~ CanonicalN x

instance Semigroupoid (≤) where
  E ∘ r = r
  B l ∘ r = B (l ∘ r)

instance Category (≤) where
  identity _ = E
