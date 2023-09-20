{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Defs where

import Data.Kind
import Data.Proxy
import Prelude qualified

{- Category: definition -}

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Lookup the type of a category's object names
type NamesOf :: forall i. CATEGORY i -> Type
type NamesOf (c :: CATEGORY i) = i

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k

-- Semigroupoids have a means of composing arrows
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- Categories are Semigroupoids with an identity arrow
type Category :: CATEGORY i -> Constraint
class Semigroupoid k => Category k where
  identity_ :: i ∈ k => k i i

identity :: forall i k. (Category k, i ∈ k) => k i i
identity = identity_

{- Monoid: definition -}

-- Monoids are categories with a single object
class (Category c, o ∈ c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i) (o :: i)

instance (Category c, o ∈ c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i) (o :: i)

{- Category: types -}

type Types = (->) :: CATEGORY Type

type instance t ∈ Types = (t ~ t)

instance Semigroupoid Types where
  (∘) = (Prelude..)

instance Category Types where
  identity_ = Prelude.id

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
type Act :: ((d :: CATEGORY i) --> (c :: CATEGORY j)) -> i -> j
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ CodomainOf f) => Acts f o

instance (Act f o ∈ CodomainOf f) => Acts f o

-- A functor is functorial for some object name.
-- If `o` is an object in `f`'s domain category,
-- then `f` acting on `o` is an object in `f`'s codomain category
type Functorial :: ((d :: CATEGORY o) --> c) -> o -> Constraint
type Functorial f o = (o ∈ DomainOf f => Acts f o)

-- What is a functor?
-- DomainOf must be a category.
-- CodomainOf must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
type Functor :: (d --> c) -> Constraint
class (Category d, Category c, forall o. Functorial f o) => Functor (f :: d --> c) where
  map_ :: (a ∈ d, b ∈ d) => d a b -> c (Act f a) (Act f b)

-- map but easier to type-apply with the functor name
map ::
  forall {d} {c} (f :: d --> c) a b.
  (Functor f, a ∈ d, b ∈ d) =>
  d a b ->
  c (Act f a) (Act f b)
map d = map_ @_ @_ @f d

{- Category: opposites -}

data Op :: CATEGORY i -> CATEGORY i where
  OP :: {runOP :: k b a} -> Op k a b

type instance i ∈ Op k = i ∈ k

instance Semigroupoid k => Semigroupoid (Op k) where
  OP g ∘ OP f = OP (f ∘ g)

instance Category k => Category (Op k) where
  identity_ = OP identity

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
  identity_ = identity :×: identity

{- Category: exponentials -}

data (^) :: forall c d -> CATEGORY (d --> c) where
  EXP ::
    { unExp :: forall i. i ∈ d => Proxy i -> c (Act f i) (Act g i)
    } ->
    (c ^ d) f g

type (~>) (f :: d --> c) g = (c ^ d) f g

runExp :: forall x c d i o. (x ∈ d) => (c ^ d) i o -> c (Act i x) (Act o x)
runExp (EXP f) = f (Proxy :: Proxy x)

type instance o ∈ (c ^ d) = Functor o

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = EXP \p -> unExp l p ∘ unExp r p

instance (Category d, Category c) => Category (c ^ d) where
  identity_ = EXP \_ -> identity

{- Functor: identity -}

data Id :: forall k. k --> k

type instance Act Id x = x

instance Category k => Functor (Id :: k --> k) where
  map_ f = f

{- Functor: composition as an operation -}

data (∘) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f ∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f ∘ map @g

{- Category: Cat -}

data Cat :: forall k. CATEGORY (CATEGORY k) where
  CAT :: Functor (f :: a --> b) => Proxy f -> Cat a b

type instance c ∈ Cat = Category c

instance Semigroupoid Cat where
  CAT (Proxy :: Proxy f) ∘ CAT (Proxy :: Proxy g) =
    CAT (Proxy @(f ∘ g))

instance Category Cat where
  identity_ = CAT (Proxy @Id)

{- Functor: composition as a functor -}

above ::
  forall {c} {d} k (f :: c --> d) g.
  (Functor k) =>
  (f ~> g) ->
  ((f ∘ k) ~> (g ∘ k))
above fg = EXP \(_ :: Proxy i) -> runExp @(Act k i) fg

beneath ::
  forall {c} {d} k (f :: c --> d) g.
  (Functor f, Functor g, Functor k) =>
  (f ~> g) ->
  ((k ∘ f) ~> (k ∘ g))
beneath fg = EXP (map @k ∘ unExp fg)

-- Functor in the two functors arguments
-- `(f ∘ g) v` is a functor in `f`, and `g`
data Compose :: forall a b x. ((b ^ a) × (a ^ x)) --> (b ^ x)

-- `(f ∘ g) v` is a functor in `f`, `g`, and `v`
data Composed :: forall a b c. (((b ^ a) × (a ^ c)) × c) --> b

type instance Act (Compose @a @b @x) e = Fst e ∘ Snd e

type instance Act (Composed @a @b @c) e = Act (Act Compose (Fst e)) (Snd e)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Compose @aa @bb @cc)
  where
  map_ ((fh :: f ~> h) :×: (gi :: g ~> i)) =
    beneath @h gi ∘ above @g fh :: (f ∘ g) ~> (h ∘ i)

instance
  (Category aa, Category bb, Category cc) =>
  Functor (Composed @aa @bb @cc)
  where
  map_ (fhgi :×: (xy :: cc x y)) =
    case map @(Compose @aa @bb) fhgi of
      (v :: (f ∘ g) ~> (h ∘ i)) ->
        map @(h ∘ i) xy ∘ runExp @x v

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
  map_ byz = map @f (identity @x :×: byz)

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry_ @a @b @c f)
  where
  map_ axy = EXP \(_p :: Proxy i) ->
    map @f (axy :×: identity @i)

instance
  (Category a, Category b, Category c) =>
  Functor (Curry @a @b @c)
  where
  map_ (EXP t) = EXP \(_p :: Proxy i) ->
    EXP \(_q :: Proxy j) ->
      t (Proxy @'(i, j))

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
  leftAdjoint_ ::
    forall a b.
    (a ∈ c, b ∈ d) =>
    c a (Act g b) ->
    d (Act f a) b
  rightAdjoint_ ::
    forall a b.
    (a ∈ c, b ∈ d) =>
    d (Act f a) b ->
    c a (Act g b)

leftAdjoint ::
  forall {c} {d} f (g :: d --> c) a b.
  ( f ⊣ g,
    a ∈ c,
    b ∈ d
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjoint = leftAdjoint_ @c @d @f @g

rightAdjoint ::
  forall {c} {d} f (g :: d --> c) a b.
  ( f ⊣ g,
    a ∈ c,
    b ∈ d
  ) =>
  d (Act f a) b ->
  c a (Act g b)
rightAdjoint = rightAdjoint_ @c @d @f @g

{- Monad & Comonad -}

type MidCompositionIx :: forall c. (c --> c) -> Type
type family MidCompositionIx m where
  MidCompositionIx (g ∘ f) = NamesOf (DomainOf g)

type MidComposition :: forall c. forall (m :: c --> c) -> CATEGORY (MidCompositionIx m)
type family MidComposition m where
  MidComposition (g ∘ f) = DomainOf g

type Outer :: forall c. forall (m :: c --> c) -> (MidComposition m --> c)
type family Outer m where
  Outer (g ∘ f) = g

type Inner :: forall c. forall (m :: c --> c) -> (c --> MidComposition m)
type family Inner m where
  Inner (g ∘ f) = f

type TheComposition :: forall c. (c --> c) -> (c --> c)
type TheComposition m = Outer m ∘ Inner m

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
type Invert m = Inner m ∘ Outer m

unit ::
  forall {c} (m :: c --> c) a {f} {g}.
  (Monad m, m ~ (g ∘ f), a ∈ c) =>
  c a (Act m a)
unit = rightAdjoint @f @g identity

counit ::
  forall {d} (w :: d --> d) a {f} {g}.
  (Comonad w, w ~ (f ∘ g), a ∈ d) =>
  d (Act w a) a
counit = leftAdjoint @f @g identity

join ::
  forall {c} (m :: c --> c) a {f} {g}.
  (m ~ (g ∘ f), f ⊣ g, a ∈ c) =>
  c (Act (m ∘ m) a) (Act m a)
join = map @g (counit @(Invert m) @(Act f a))

extend ::
  forall {d} (w :: d --> d) a {f} {g}.
  (w ~ (f ∘ g), f ⊣ g, a ∈ d) =>
  d (Act w a) (Act (w ∘ w) a)
extend = map @f (unit @(Invert w) @(Act g a))

flatMap ::
  forall {c} (m :: c --> c) a b {f} {g}.
  (m ~ (g ∘ f), f ⊣ g, a ∈ c, b ∈ c) =>
  c a (Act m b) ->
  c (Act m a) (Act m b)
flatMap amb = join @m @b ∘ map @m amb

{- Category: 1 -}

data One :: CATEGORY () where
  ONE :: One '() '()

type instance t ∈ One = (t ~ '())

instance Semigroupoid One where
  ONE ∘ ONE = ONE

instance Category One where
  identity_ = ONE

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
class Functor op => Associative (op :: BINARY_OP k) where
  lassoc_ ::
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      ((a ☼ (b ☼ c) op) op)
      (((a ☼ b) op ☼ c) op)
  rassoc_ ::
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      (((a ☼ b) op ☼ c) op)
      ((a ☼ (b ☼ c) op) op)

lassoc ::
  forall
    {i}
    {k :: CATEGORY i}
    (op :: BINARY_OP k)
    a
    b
    c.
  (Associative op, a ∈ k, b ∈ k, c ∈ k) =>
  k
    ((a ☼ (b ☼ c) op) op)
    (((a ☼ b) op ☼ c) op)
lassoc = lassoc_ @k @op @a @b @c

rassoc ::
  forall
    {i}
    {k :: CATEGORY i}
    (op :: BINARY_OP k)
    a
    b
    c.
  (Associative op, a ∈ k, b ∈ k, c ∈ k) =>
  k
    (((a ☼ b) op ☼ c) op)
    ((a ☼ (b ☼ c) op) op)
rassoc = rassoc_ @k @op @a @b @c

instance Category k => Associative (Compose :: BINARY_OP (k ^ k)) where
  lassoc_ = EXP \_ -> identity
  rassoc_ = EXP \_ -> identity

type Braided ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class Associative p => Braided (p :: BINARY_OP k) where
  braid :: (x ∈ k, y ∈ k) => k ((x ☼ y) p) ((y ☼ x) p)

type Symmetric ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  Constraint
class Braided p => Symmetric p

type Monoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  Constraint
class
  ( Associative p
  ) =>
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

instance Functor p => Functor (Spin p) where
  map_ (r :×: l) = map @p (l :×: r)

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
  ( forall y. y ∈ k => With² p y ⊣ With¹ e y,
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
  MonoidObject p id m =>
  k id m
empty = empty_ @k @p @id @m

append ::
  forall {i} {k :: CATEGORY i} (p :: BINARY_OP k) {id :: i} (m :: i).
  MonoidObject p id m =>
  k ((☼) m m p) m
append = append_ @k @p @id @m

instance
  Category k =>
  Monoidal Compose (Id :: k --> k)
  where
  idl = EXP \_ -> identity
  coidl = EXP \_ -> identity
  idr = EXP \_ -> identity
  coidr = EXP \_ -> identity

instance
  ( Monad m,
    m ~ (f ∘ g)
  ) =>
  MonoidObject Compose Id m
  where
  empty_ = EXP \_ -> unit @m
  append_ = EXP \(_p :: Proxy i) -> join @m @i

{- fixed point functors -}

class Functor (Fixed k :: (k ^ k) --> k) => HasFixed (k :: CATEGORY i) where
  type Fixed k :: (k ^ k) --> k
  wrap_ :: forall (f :: k --> k). Functor f => k (Act f (Act (Fixed k) f)) (Act (Fixed k) f)
  unwrap_ :: forall (f :: k --> k). Functor f => k (Act (Fixed k) f) (Act f (Act (Fixed k) f))

wrap :: forall {k} (f :: k --> k). (HasFixed k, Functor f) => k (Act f (Act (Fixed k) f)) (Act (Fixed k) f)
wrap = wrap_ @_ @k @f

unwrap :: forall {k} (f :: k --> k). (HasFixed k, Functor f) => k (Act (Fixed k) f) (Act f (Act (Fixed k) f))
unwrap = unwrap_ @_ @k @f

cata ::
  forall {k} (f :: k --> k) a.
  (HasFixed k, Functor f, a ∈ k) =>
  k (Act f a) a ->
  k (Act (Fixed k) f) a
cata t = go where go = t ∘ map @f go ∘ unwrap @f

data DataFix f = In {out :: Act f (DataFix f)}

data Fix :: (Types ^ Types) --> Types

type instance Act Fix f = DataFix f

instance Functor Fix where
  map_ :: forall a b. (Functor a, Functor b) => (a ~> b) -> (Act Fix a) -> (Act Fix b)
  map_ t = In ∘ map @b (map @Fix t) ∘ runExp @(Act Fix a) t ∘ out

instance HasFixed Types where
  type Fixed Types = Fix
  wrap_ = In
  unwrap_ = out
