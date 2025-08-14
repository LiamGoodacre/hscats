{-# LANGUAGE StrictData #-}

module Defs where

import Data.Kind (Constraint, Type)
import Data.Proxy (Proxy (Proxy))
import Data.Type.Equality ((:~:) (Refl), type (~))
import Prelude qualified

{- Category: definition -}

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Lookup the type of a category's object names
type NamesOf :: forall i. CATEGORY i -> Type
type NamesOf @i c = i

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k

-- Semigroupoids have a means of composing arrows
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- Categories are Semigroupoids with an identity arrow
type Category :: CATEGORY i -> Constraint
class (Semigroupoid k) => Category k where
  identity :: forall o -> (o ∈ k) => k o o

{- Monoid: definition -}

-- Monoids are categories with a single object
type Monoid :: CATEGORY i -> i -> Constraint
class (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

instance (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

{- Category: types -}

type Types = (->) :: CATEGORY Type

type instance t ∈ Types = (t ~ t)

instance Semigroupoid Types where
  (∘) = (Prelude..)

instance Category Types where
  identity _ = Prelude.id

{- Category: equality -}

-- "Equality" forms a category
type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity _ = Refl

{- Functor: definition -}

-- Type of functors indexed by domain & codomain categories
type (-->) :: forall i j. CATEGORY i -> CATEGORY j -> Type
type (-->) d c = Proxy d -> Proxy c -> Type

-- Project the domain category of a functor
type DomainOf :: forall i (d :: CATEGORY i) c. (d --> c) -> CATEGORY i
type DomainOf (f :: d --> c) = d

-- Project the codomain category of a functor
type CodomainOf :: forall j d (c :: CATEGORY j). (d --> c) -> CATEGORY j
type CodomainOf (f :: d --> c) = c

-- Functors act on object names
type Act :: (d --> c) -> NamesOf d -> NamesOf c
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ CodomainOf f) => Acts f o

instance (Act f o ∈ CodomainOf f) => Acts f o

-- What is a functor?
-- DomainOf must be a category.
-- CodomainOf must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
type Functor :: (d --> c) -> Constraint
class (Category d, Category c, forall o. (o ∈ DomainOf f) => Acts f o) => Functor (f :: d --> c) where
  map ::
    forall f' ->
    (f' ~ f, a ∈ d, b ∈ d) =>
    d a b -> c (Act f a) (Act f b)

type OnActing ::
  forall {d} {k}.
  (NamesOf k -> Constraint) ->
  (d --> k) ->
  NamesOf d ->
  Constraint
class (c (Act f x)) => OnActing c f x

instance (c (Act f x)) => OnActing c f x

{- Referencing special objects -}

type OBJECT :: forall i. CATEGORY i -> Type
type OBJECT k = Proxy k -> Type

type ObjectName :: OBJECT k -> NamesOf k
type family ObjectName o

data AnObject :: forall (k :: CATEGORY i) -> NamesOf k -> OBJECT k

type instance ObjectName (AnObject k n) = n

{- Category: opposites -}

data Op :: CATEGORY i -> CATEGORY i where
  OP :: {runOP :: k b a} -> Op k a b

type instance i ∈ Op k = i ∈ k

instance (Semigroupoid k) => Semigroupoid (Op k) where
  OP g ∘ OP f = OP (f ∘ g)

instance (Category k) => Category (Op k) where
  identity o = OP (identity o)

{- Category: products -}

data (×) :: CATEGORY s -> CATEGORY t -> CATEGORY (s, t) where
  (:×:) :: l a b -> r x y -> (l × r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type instance v ∈ (l × r) = (v ~ '(Fst v, Snd v), Fst v ∈ l, Snd v ∈ r)

instance (Semigroupoid l, Semigroupoid r) => Semigroupoid (l × r) where
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

instance (Category l, Category r) => Category (l × r) where
  identity (a, b) = identity a :×: identity b

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

{- Functor: identity -}

data Id :: forall k. k --> k

type instance Act Id x = x

instance (Category k) => Functor (Id :: k --> k) where
  map _ f = f

{- Functor: composition as an operation -}

data (•) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f • g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f • g) where
  map _ = map f ∘ map g

{- Category: Cat -}

data Cat :: forall k. CATEGORY (CATEGORY k) where
  CAT :: (Functor (f :: a --> b)) => Proxy f -> Cat a b

type instance c ∈ Cat = Category c

instance Semigroupoid Cat where
  CAT (Proxy @f) ∘ CAT (Proxy @g) =
    CAT (Proxy @(f • g))

instance Category Cat where
  identity _ = CAT (Proxy @Id)

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

type instance Act Eval fx = Act (Fst fx) (Snd fx)

data Curry__ :: forall a b c. ((a × b) --> c) -> NamesOf a -> (b --> c)

type instance Act (Curry__ f x) y = Act f '(x, y)

data Curry_ :: forall a b c. ((a × b) --> c) -> (a --> (c ^ b))

type instance Act (Curry_ f) x = Curry__ f x

data Curry :: forall a b c. (c ^ (a × b)) --> ((c ^ b) ^ a)

type instance Act Curry f = Curry_ f

instance
  (Category a, Category b, Functor f, x ∈ a) =>
  Functor (Curry__ @a @b @c f x)
  where
  map _ byz = map f (identity x :×: byz)

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry_ @a @b @c f)
  where
  map _ axy = EXP \i ->
    map f (axy :×: identity i)

instance
  (Category a, Category b, Category c) =>
  Functor (Curry @a @b @c)
  where
  map _ (EXP t) = EXP \i -> EXP \j -> t (i, j)

{- Adjunctions -}

-- Two functors f and g are adjoint when
--   `∀ a b. (a → g b) ⇔ (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) ⇔ d (Act f a) b`
--
-- Typing '⊣': `^q u 22A3` or `^v u 22A3`
--

type (⊣) :: (c --> d) -> (d --> c) -> Constraint
class
  (Functor f, Functor g) =>
  f ⊣ (g :: d --> c)
    | f -> g,
      g -> f
  where
  leftAdjoint ::
    forall g' f' ->
    (f' ~ f, g' ~ g) =>
    (a ∈ c, b ∈ d) =>
    c a (Act g b) ->
    d (Act f a) b
  rightAdjoint ::
    forall f' g' ->
    (f' ~ f, g' ~ g) =>
    (a ∈ c, b ∈ d) =>
    d (Act f a) b ->
    c a (Act g b)

{- Monad & Comonad -}

type MidCompositionIx :: forall c. (c --> c) -> Type
type family MidCompositionIx m where
  MidCompositionIx (g • f) = NamesOf (DomainOf g)

type MidComposition :: forall c. forall (m :: c --> c) -> CATEGORY (MidCompositionIx m)
type family MidComposition m where
  MidComposition (g • f) = DomainOf g

type Outer :: forall c. forall (m :: c --> c) -> (MidComposition m --> c)
type family Outer m where
  Outer (g • f) = g

type Inner :: forall c. forall (m :: c --> c) -> (c --> MidComposition m)
type family Inner m where
  Inner (g • f) = f

type TheComposition :: forall c. (c --> c) -> (c --> c)
type TheComposition m = Outer m • Inner m

type Monad :: forall c. (c --> c) -> Constraint
type Monad m =
  ( m ~ TheComposition m,
    Inner m ⊣ Outer m,
    Functor m
  )

type Comonad :: forall c. (c --> c) -> Constraint
type Comonad w =
  ( w ~ TheComposition w,
    Outer w ⊣ Inner w,
    Functor w
  )

type Invert :: forall c. forall (m :: c --> c) -> (MidComposition m --> MidComposition m)
type Invert m = Inner m • Outer m

unit ::
  forall {c} g f.
  forall (m :: c --> c) a ->
  (m ~ (g • f), Monad (g • f), a ∈ c) =>
  c a (Act m a)
unit _ a = rightAdjoint f g (identity (Act f a))

counit ::
  forall {d} f g.
  forall (w :: d --> d) a ->
  (Comonad w, w ~ (f • g), a ∈ d) =>
  d (Act w a) a
counit _ a = leftAdjoint g f (identity (Act g a))

join ::
  forall {c} f g.
  forall (m :: c --> c) a ->
  (m ~ (g • f), f ⊣ g, a ∈ c) =>
  c (Act (m • m) a) (Act m a)
join m a = map g (counit (Invert m) (Act f a))

extend ::
  forall {d} f g.
  forall (w :: d --> d) a ->
  (w ~ (f • g), f ⊣ g, a ∈ d) =>
  d (Act w a) (Act (w • w) a)
extend w a = map f (unit (Invert w) (Act g a))

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

type BINARY_OP k = (k × k) --> k

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

data Spin :: BINARY_OP k -> BINARY_OP k

type instance Act (Spin p) x = Act p '(Snd x, Fst x)

instance (Functor p) => Functor (Spin p) where
  map _ (r :×: l) = map p (l :×: r)

type With¹ p = Curry__ p

type With² p = Curry__ (Spin p)

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
