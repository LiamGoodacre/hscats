{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Kind
import Data.Proxy
import Prelude (Either (..), Int, Num (..), String, fromInteger, undefined, ($), (.), (<>))
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
  identity :: i ∈ k => k i i

{- Category: Examples -}

data One :: CATEGORY () where
  ONE :: One '() '()

type instance t ∈ One = (t ~ '())

instance Semigroupoid One where
  ONE ∘ ONE = ONE

instance Category One where
  identity = ONE

-- "Equality" forms a category
data (:~:) :: CATEGORY t where
  Refl :: x :~: x

type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity = Refl

-- There's a category Types.
-- Whose objects are types,
-- and arrows are functions.
type Types = (->) :: CATEGORY Type

type instance t ∈ Types = (t ~ t)

instance Semigroupoid Types where
  (∘) = (.)

instance Category Types where
  identity = Prelude.id

-- Every category has an opposite
data Op :: CATEGORY i -> CATEGORY i where
  Op :: k b a -> Op k a b

type instance i ∈ Op k = i ∈ k

instance Semigroupoid k => Semigroupoid (Op k) where
  Op g ∘ Op f = Op (f ∘ g)

instance Category k => Category (Op k) where
  identity = Op identity

-- The cross-product of two categories, is a category
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
  identity = identity :×: identity

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
  identity = E

{- Monoid: definition -}

-- Monoids are categories with a single object
class (Category c, o ∈ c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i) (o :: i)

instance (Category c, o ∈ c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i) (o :: i)

{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: m -> PreludeMonoid m '() '()

type instance x ∈ PreludeMonoid m = (x ~ '())

instance Prelude.Semigroup m => Semigroupoid (PreludeMonoid m) where
  PreludeMonoid l ∘ PreludeMonoid r = PreludeMonoid (l <> r)

instance Prelude.Monoid m => Category (PreludeMonoid m) where
  identity = PreludeMonoid Prelude.mempty

data Endo :: i -> CATEGORY i -> CATEGORY () where
  Endo :: c o o -> Endo o c '() '()

type instance x ∈ Endo o c = (x ~ '())

instance (Semigroupoid c, o ∈ c) => Semigroupoid (Endo o c) where
  Endo l ∘ Endo r = Endo (l ∘ r)

instance (Category c, o ∈ c) => Category (Endo o c) where
  identity = Endo identity

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

{- Functor: examples -}

-- The identity functor for some category k
data Id :: forall k. k --> k

type instance Act Id x = x

instance Category k => Functor (Id :: k --> k) where
  map_ f = f

-- Composing two compatible functors, is a functor
data (∘) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f ∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f . map @g

-- Prelude.Functor is a specialisation of Functor
data PreludeFunctor (f :: Type -> Type) :: Types --> Types

type instance Act (PreludeFunctor f) a = f a

instance Prelude.Functor f => Functor (PreludeFunctor f) where
  map_ = Prelude.fmap

-- Parallel functor product

data (***) :: (a --> s) -> (b --> t) -> ((a × b) --> (s × t))

type instance Act (f *** g) o = '(Act f (Fst o), Act g (Snd o))

instance (Functor f, Functor g) => Functor (f *** g) where
  map_ (l :×: r) = map @f l :×: map @g r

-- Pointwise functor product

data (&&&) :: (d --> l) -> (d --> r) -> (d --> (l × r))

type instance Act (f &&& g) o = '(Act f o, Act g o)

instance (Functor f, Functor g) => Functor (f &&& g) where
  map_ t = map @f t :×: map @g t

-- Some Yoneda embeddings
data YoCodomain :: forall (k :: CATEGORY i) -> i -> (k --> Types)

type instance Act (YoCodomain k d) c = k d c

instance (d ∈ k, Category k) => Functor (YoCodomain k d) where
  map_ = (∘)

data YoDomain :: forall (k :: CATEGORY i) -> i -> (Op k --> Types)

type instance Act (YoDomain k c) d = k d c

instance (d ∈ k, Category k) => Functor (YoDomain k d) where
  map_ (Op g) f = f ∘ g

data Hom :: forall (k :: CATEGORY i) -> ((Op k × k) --> Types)

type instance Act (Hom k) o = k (Fst o) (Snd o)

instance Category k => Functor (Hom k) where
  map_ (Op f :×: g) t = g ∘ t ∘ f

-- Foldable?

class Foldable t where
  foldMap :: (Monoid c o) => (a -> c o o) -> Act t a -> c o o

data List :: Types --> Types

type instance Act List t = [t]

instance Functor List where
  map_ = Prelude.fmap

instance Foldable List where
  foldMap _ [] = identity
  foldMap f (h : t) = f h ∘ foldMap @List f t

{- Exponential category / natural transformations -}

data (^) :: forall c d -> CATEGORY (d --> c) where
  Exp ::
    (forall i. i ∈ d => Proxy i -> c (Act f i) (Act g i)) ->
    (c ^ d) f g

type (~>) (f :: d --> c) g = (c ^ d) f g

runExp :: forall x c d i o. (x ∈ d) => (c ^ d) i o -> c (Act i x) (Act o x)
runExp (Exp f) = f (Proxy :: Proxy x)

type instance o ∈ (c ^ d) = Functor o

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = Exp \p -> case (l, r) of
    (Exp f, Exp g) -> (f p ∘ g p)

instance (Category d, Category c) => Category (c ^ d) where
  identity = Exp \_ -> identity

-- Functor composition is itself a functor
data FunctorCompose :: forall a b x. ((b ^ a) × (a ^ x)) --> (b ^ x)

type instance Act (FunctorCompose @a @b @x) e = Fst e ∘ Snd e

instance (Category a, Category b, Category x) => Functor (FunctorCompose @a @b @x) where
  -- map_ (Exp t :×: Exp s) = Exp \_ -> t Proxy ∘ s Proxy
  map_ _ = undefined

{- Adjunctions -}

-- Two functors f and g are adjoint when
--   `∀ a b. (a → g b) ⇔ (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) ⇔ d (Act f a) b`
--
-- Typing '⊣': `^q u 22A3` or `^v u 22A3`
--
type (⊣) :: (c --> d) -> (d --> c) -> Constraint
class (Functor f, Functor g) => f ⊣ (g :: d --> c) | f -> g, g -> f where
  leftAdjoint_ :: forall a b. (a ∈ c, b ∈ d) => c a (Act g b) -> d (Act f a) b
  rightAdjoint_ :: forall a b. (a ∈ c, b ∈ d) => d (Act f a) b -> c a (Act g b)

leftAdjoint ::
  forall {c} {d} (f :: c --> d) (g :: d --> c) a b.
  ( f ⊣ g,
    a ∈ c,
    b ∈ d
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjoint = leftAdjoint_ @c @d @f @g

rightAdjoint ::
  forall {c} {d} (f :: c --> d) (g :: d --> c) a b.
  ( f ⊣ g,
    a ∈ c,
    b ∈ d
  ) =>
  d (Act f a) b ->
  c a (Act g b)
rightAdjoint = rightAdjoint_ @c @d @f @g

unit ::
  forall
    {c}
    {d}
    (m :: c --> c)
    {f :: c --> d}
    {g :: d --> c}
    a.
  ( m ~ (g ∘ f),
    f ⊣ g,
    a ∈ c
  ) =>
  c a (Act m a)
unit = rightAdjoint @f @g identity

counit ::
  forall
    {c}
    {d}
    (w :: d --> d)
    {f :: c --> d}
    {g :: d --> c}
    a.
  ( w ~ (f ∘ g),
    f ⊣ g,
    a ∈ d
  ) =>
  d (Act w a) a
counit = leftAdjoint @f @g identity

join ::
  forall
    {c}
    {d}
    {f :: c --> d}
    {g :: d --> c}
    (m :: c --> c)
    a.
  ( m ~ (g ∘ f),
    f ⊣ g,
    a ∈ c
  ) =>
  c (Act (m ∘ m) a) (Act m a)
join = do
  let t :: d (Act (f ∘ g ∘ f) a) (Act f a)
      t = counit @(f ∘ g)
  map @g t

extend ::
  forall
    {c}
    {d}
    {f :: c --> d}
    {g :: d --> c}
    (w :: d --> d)
    a.
  ( w ~ (f ∘ g),
    f ⊣ g,
    a ∈ d
  ) =>
  d (Act w a) (Act (w ∘ w) a)
extend = do
  let t :: c (Act g a) (Act (g ∘ f ∘ g) a)
      t = unit @(g ∘ f)
  map @f t

flatMap ::
  forall
    {d}
    (m :: Types --> Types)
    a
    b
    {f :: Types --> d}
    {g :: d --> Types}.
  ( m ~ (g ∘ f),
    f ⊣ g
  ) =>
  Proxy b ->
  Act m a ->
  (a -> Act m b) ->
  Act m b
flatMap _ m t =
  join @m @b
    (map @m t m :: Act (m ∘ m) b)

{- Adjunctions: examples -}

-- Env s ⊣ Reader s

data Reader :: Type -> (Types --> Types)

type instance Act (Reader x) y = x -> y

instance Functor (Reader x) where
  map_ = (.)

data Env :: Type -> (Types --> Types)

type instance Act (Env x) y = (y, x)

instance Functor (Env x) where
  map_ f (l, r) = (f l, r)

instance Env s ⊣ Reader s where
  leftAdjoint_ = Prelude.uncurry
  rightAdjoint_ = Prelude.curry

-- (∨) ⊣ Δ Types ⊣ (∧)

data Δ :: forall (k :: CATEGORY i) -> (k --> (k × k))

type instance Act (Δ k) x = '(x, x)

instance Category k => Functor (Δ k) where
  map_ f = (f :×: f)

data (∧) :: (Types × Types) --> Types

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map_ (f :×: g) (a, b) = (f a, g b)

data (∨) :: (Types × Types) --> Types

type instance Act (∨) x = Either (Fst x) (Snd x)

instance Functor (∨) where
  map_ (f :×: g) = Prelude.either (Left . f) (Right . g)

instance Δ Types ⊣ (∧) where
  leftAdjoint_ t = (Prelude.fst . t) :×: (Prelude.snd . t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ Types where
  leftAdjoint_ (f :×: g) = f `Prelude.either` g
  rightAdjoint_ t = (t . Left) :×: (t . Right)

-- (∘ g) ⊣ (/ g)
-- aka (PostCompose g ⊣ PostRan g)

data PostCompose :: (c --> c') -> (a ^ c') --> (a ^ c)

type instance Act (PostCompose g) f = f ∘ g

instance
  (Category c, Category c', Category a, Functor g) =>
  Functor (PostCompose @c @c' @a g)
  where
  map_ (Exp h) = Exp \(Proxy :: Proxy i) -> h (Proxy @(Act g i))

type Ran :: (x --> Types) -> (x --> z) -> NamesOf z -> Type
data Ran h g a where
  Ran ::
    Functor f =>
    Proxy f ->
    ((f ∘ g) ~> h) ->
    Act f a ->
    Ran h g a

-- NOTE: currently y is always Types
data (/) :: (x --> y) -> (x --> z) -> (z --> y)

type instance Act (h / g) o = Ran h g o

instance (Category x, Category z) => Functor ((/) @x @Types @z h g) where
  map_ zab (Ran (pf :: Proxy f) fgh fa) =
    Ran pf fgh (map @f zab fa)

-- NOTE: currently y is always Types
data PostRan :: (x --> z) -> (y ^ x) --> (y ^ z)

type instance Act (PostRan g) h = h / g

instance
  (Category x, Category z, Functor g) =>
  Functor (PostRan @x @z @Types g)
  where
  map_ ab =
    Exp \_ (Ran p fga fi) ->
      Ran p (ab ∘ fga) fi

instance (Functor g) => PostCompose g ⊣ PostRan @x @z @Types g where
  leftAdjoint_ a_bg =
    Exp \(Proxy :: Proxy i) ag ->
      case runExp @(Act g i) a_bg ag of
        Ran _ fg_b fgi ->
          runExp @i fg_b fgi

  rightAdjoint_ ag_b =
    Exp \(Proxy :: Proxy i) (a :: Act a i) ->
      Ran (Proxy @a) ag_b a

type Codensity :: (x --> Types) -> (Types --> Types)
type Codensity f = f / f

--

-- Monad & Comonad
type MidCompositionIx :: forall c. (c --> c) -> Type
type family MidCompositionIx m where
  MidCompositionIx (g ∘ f) = NamesOf (CodomainOf f)

type MidComposition :: forall c. forall (m :: c --> c) -> CATEGORY (MidCompositionIx m)
type family MidComposition m where
  MidComposition (g ∘ f) = CodomainOf f

type Outer :: forall c. forall (m :: c --> c) -> (MidComposition m --> c)
type family Outer m where
  Outer (g ∘ f) = g

type Inner :: forall c. forall (m :: c --> c) -> (c --> MidComposition m)
type family Inner m where
  Inner (g ∘ f) = f

type TheComposition :: forall c. (c --> c) -> (c --> c)
type TheComposition m = Outer m ∘ Inner m

type Monad :: forall c. (c --> c) -> Constraint
type Monad m = (m ~ TheComposition m, Inner m ⊣ Outer m, Functor m)

type Comonad :: forall c. (c --> c) -> Constraint
type Comonad w = (w ~ TheComposition w, Outer w ⊣ Inner w, Functor w)

-- do notationy stuff

newtype BindDo m
  = BindDo
      ( forall a b.
        Proxy b ->
        Act m a ->
        (a -> Act m b) ->
        Act m b
      )

newtype PureDo m
  = PureDo
      (forall a. a -> Act m a)

type MonadDo m =
  forall r.
  ( ( ?bind :: BindDo m,
      ?pure :: PureDo m
    ) =>
    Act m r
  ) ->
  Act m r

(>>=) :: forall m a b. (?bind :: BindDo m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let BindDo f = ?bind in f @a (Proxy @b)

pure :: forall m a. (?pure :: PureDo m) => a -> Act m a
pure = let PureDo u = ?pure in u

makeBind ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g ∘ f)) =>
  BindDo m
makeBind = BindDo (flatMap @m)

makePure ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g ∘ f)) =>
  PureDo m
makePure = PureDo (unit @m)

monadDo ::
  forall (m :: Types --> Types) {f} {g}.
  (Monad m, m ~ (g ∘ f)) =>
  MonadDo m
monadDo t = do
  let ?bind = makeBind @m
  let ?pure = makePure @m
  t

---

type Dup = (∧) ∘ Δ Types

dupMonad :: MonadDo Dup
dupMonad = monadDo

egDuped :: (Int, Int)
egDuped = monadDo @Dup do
  v <- (10, 100)
  x <- (v + 1, v + 2)
  pure (x * 2)

-- $> egDuped -- (22,204)

type States s = Reader s ∘ Env s

stateMonad :: MonadDo (States s)
stateMonad = monadDo

type State s i = Act (States s) i

get :: State s s
get s = (s, s)

put :: s -> State s ()
put v _ = ((), v)

modify :: (s -> s) -> State s ()
modify t s = ((), t s)

postinc :: State Int Int
postinc = stateMonad do
  x <- get
  _ <- put (x + 1)
  pure x

twicePostincShow :: State Int String
twicePostincShow = stateMonad do
  a <- postinc
  b <- postinc
  c <- pure $ dupMonad do
    v <- (10, 100)
    x <- (v + 1, v + 2)
    pure (x * 2 :: Int)
  pure (Prelude.show a <> "-" <> Prelude.show b <> "-" <> Prelude.show c)

egState :: (String, Int)
egState = twicePostincShow 10

-- $> egState

newtype NT t m = NT (t ~> m)

type Free :: (Types --> Types) -> Type -> Type
data Free t a = Free
  { runFree ::
      forall m.
      Monad m =>
      Proxy m ->
      Proxy a ->
      NT t m ->
      Act m a
  }

data Free0 :: (k --> k) -> (k --> k)

data Free1 :: (k ^ k) --> (k ^ k)

type instance Act (Free0 f) o = Free f o

type instance Act Free1 f = Free0 f

instance Functor (Free0 @Types t) where
  map_ (a_b :: a -> b) r = Free do
    let outer ::
          forall m.
          Monad m =>
          Proxy m ->
          Proxy b ->
          NT t m ->
          Act m b
        outer pm _pb tm =
          map @m a_b (runFree r pm (Proxy @a) tm)
    outer

instance Functor (Free1 @Types) where
  map_ = undefined

---

type Associative ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  Constraint
class Functor op => Associative (op :: (k × k) --> k) where
  lassoc_ ::
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      (Act op '(a, Act op '(b, c)))
      (Act op '(Act op '(a, b), c))
  rassoc_ ::
    (a ∈ k, b ∈ k, c ∈ k) =>
    k
      (Act op '(Act op '(a, b), c))
      (Act op '(a, Act op '(b, c)))

lassoc ::
  forall
    {i}
    {k :: CATEGORY i}
    (op :: (k × k) --> k)
    a
    b
    c.
  (Associative op, a ∈ k, b ∈ k, c ∈ k) =>
  k
    (Act op '(a, Act op '(b, c)))
    (Act op '(Act op '(a, b), c))
lassoc = lassoc_ @k @op @a @b @c

rassoc ::
  forall
    {i}
    {k :: CATEGORY i}
    (op :: (k × k) --> k)
    a
    b
    c.
  (Associative op, a ∈ k, b ∈ k, c ∈ k) =>
  k
    (Act op '(Act op '(a, b), c))
    (Act op '(a, Act op '(b, c)))
rassoc = rassoc_ @k @op @a @b @c

type Monoidal ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  (One --> k) ->
  Constraint
class
  ( Associative p,
    Functor id
  ) =>
  Monoidal p (id :: One --> k)
  where
  idl :: (m ∈ k) => k (Act p '(Act id '(), m)) m
  coidl :: (m ∈ k) => k m (Act p '(Act id '(), m))
  idr :: (m ∈ k) => k (Act p '(m, Act id '())) m
  coidr :: (m ∈ k) => k m (Act p '(m, Act id '()))

type MonoidObject ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  (One --> k) ->
  i ->
  Constraint
class
  ( Monoidal p id,
    m ∈ k
  ) =>
  MonoidObject p (id :: One --> k) m
  where
  mempty :: k (Act id '()) m
  mappend :: k (Act p '(m, m)) m

data Unit :: One --> Types

type instance Act Unit x = ()

instance Functor Unit where
  map_ ONE = \x -> x

instance Associative (∧) where
  lassoc_ = \(a, (b, c)) -> ((a, b), c)
  rassoc_ = \((a, b), c) -> (a, (b, c))

instance Monoidal (∧) Unit where
  idl = \(_, m) -> m
  coidl = \m -> ((), m)
  idr = \(m, _) -> m
  coidr = \m -> (m, ())

instance Prelude.Monoid m => MonoidObject (∧) Unit m where
  mempty = \() -> Prelude.mempty
  mappend = \(l, r) -> Prelude.mappend l r

type DayD ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  (k --> Types) ->
  (k --> Types) ->
  i ->
  Type
data DayD p f g z where
  DayD :: Proxy x -> Proxy y -> k (Act p '(x, y)) z -> Act f x -> Act g y -> DayD @k p f g z

data
  DayF ::
    ((Types × Types) --> Types) ->
    (Types --> Types) ->
    (Types --> Types) ->
    (Types --> Types)

type instance Act (DayF p f g) x = DayD p f g x

instance Functor p => Functor (DayF p f g) where
  map_ (zw :: k z w) (DayD px py (xyz :: k xy z) fx gy) =
    DayD px py (zw ∘ xyz :: k xy w) fx gy

data
  Day ::
    ((Types × Types) --> Types) ->
    (((Types ^ Types) × (Types ^ Types)) --> (Types ^ Types))

type instance Act (Day p) '(f, g) = DayF p f g

instance Functor p => Functor (Day p) where
  map_ (Exp l :×: Exp r) =
    Exp \_p (DayD px py (xyz :: k xy z) fx gy) ->
      DayD
        px
        py
        xyz
        (l px fx)
        (r py gy)

data ProductD :: (Types --> Types) -> (Types --> Types) -> Type -> Type where
  ProductD ::
    Act f x ->
    Act g x ->
    ProductD f g x

data ProductF :: (Types --> Types) -> (Types --> Types) -> (Types --> Types)

type instance Act (ProductF f g) x = ProductD f g x

instance
  ( Functor f,
    Functor g
  ) =>
  Functor (ProductF f g)
  where
  map_ ab (ProductD fa ga) =
    ProductD
      (map @f ab fa)
      (map @g ab ga)

data Identity :: One --> (Types ^ Types)

type instance Act Identity t = Id

instance Functor Identity where
  map_ ONE = Exp \_ x -> x

instance Associative p => Associative (Day p) where
  lassoc_ = Exp \_p (DayD (px :: Proxy x) (_py :: Proxy y) xyz fx (DayD (pa :: Proxy a) (pb :: Proxy b) aby ga hb)) ->
    DayD
      Proxy
      pb
      ( xyz
          ∘ map @p
            ( identity :×: aby ::
                (Types × Types) '(x, Act p '(a, b)) '(x, y)
            )
          ∘ rassoc @p @x @a @b
      )
      (DayD px pa (\x -> x) fx ga)
      hb
  rassoc_ = Exp \_p (DayD (_px :: Proxy x) (py :: Proxy y) xyz (DayD (pa :: Proxy a) (pb :: Proxy b) abx fa gb) hy) ->
    DayD
      pa
      Proxy
      ( xyz
          ∘ map @p
            ( abx :×: identity ::
                (Types × Types) '(Act p '(a, b), y) '(x, y)
            )
          ∘ lassoc @p @a @b @y
      )
      fa
      (DayD pb py (\x -> x) gb hy)

instance Monoidal (Day (∧)) Identity where
  idl = Exp \_p (DayD _ _ xyz x my :: DayD (∧) Id m z) -> map @m (\y -> xyz (x, y)) my
  coidl = Exp \_p my -> DayD Proxy Proxy (\(_, y) -> y) () my
  idr = Exp \_p (DayD _ _ xyz mx y :: DayD (∧) m Id z) -> map @m (\x -> xyz (x, y)) mx
  coidr = Exp \_p mx -> DayD Proxy Proxy (\(x, _) -> x) mx ()

instance
  Prelude.Applicative m =>
  MonoidObject
    (Day (∧))
    Identity
    (PreludeFunctor m)
  where
  mempty = Exp \_p x -> Prelude.pure x
  mappend = Exp \_p (DayD _ _ xyz fx fy) -> Prelude.liftA2 (\x y -> xyz (x, y)) fx fy

---

main :: Prelude.IO ()
main = Prelude.putStrLn ""
