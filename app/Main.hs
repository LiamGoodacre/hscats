{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Kind
import Data.Proxy
import Prelude
  ( Either (..),
    IO,
    Int,
    Monoid (..),
    Num (..),
    Semigroup ((<>)),
    String,
    either,
    fromInteger,
    fst,
    id,
    putStrLn,
    show,
    snd,
    (.),
  )

-- Type of categories represented by their hom-types indexed by object names
type CAT :: Type -> Type
type CAT i = i -> i -> Type

-- Type of functors indexed by domain & codomain categories
type FUNCTOR :: forall i j. CAT i -> CAT j -> Type
type FUNCTOR d c = Proxy d -> Proxy c -> Type

-- Endofunctors domain & codomain categories are the same
type ENDO :: CAT i -> Type
type ENDO k = FUNCTOR k k

-- Project the domain category of a functor
type DOM :: forall i (d :: CAT i) c. FUNCTOR d c -> CAT i
type DOM (f :: FUNCTOR d c) = d

-- Project the codomain category of a functor
type COD :: forall j d (c :: CAT j). FUNCTOR d c -> CAT j
type COD (f :: FUNCTOR d c) = c

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CAT i -> Constraint
type family x ∈ k = o | o -> k x

type Known :: t -> Constraint
type Known t = t ~ t

-- Helper to deal with injectivity when instancing ∈
type Obj :: CAT i -> Constraint -> Constraint
type Obj k c = (Known k, c)

-- What is a category
type Cat :: CAT i -> Constraint
class Cat k where
  identity :: i ∈ k => k i i
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- Functors act on object names
type Act :: FUNCTOR (d :: CAT i) (c :: CAT j) -> i -> j
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ COD f) => Acts f o

instance (Act f o ∈ COD f) => Acts f o

-- A functor is functorial for some object name.
-- If `o` is an object in `f`'s domain category,
-- then `f` acting on `o` is an object in `f`'s codomain category
type Functorial :: FUNCTOR (d :: CAT o) c -> o -> Constraint
type Functorial f o = (o ∈ DOM f => Acts f o)

-- What is a functor?
-- Domain must be a category.
-- Codomain must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
type Functor :: FUNCTOR d c -> Constraint
class
  ( Cat d,
    Cat c,
    forall o. Functorial f o
  ) =>
  Functor (f :: FUNCTOR d c)
  where
  map_ ::
    (a ∈ d, b ∈ d) =>
    d a b ->
    c (Act f a) (Act f b)

-- map but easier to type-apply with the functor name
map ::
  forall {d} {c} (f :: FUNCTOR d c) a b.
  (Functor f, a ∈ d, b ∈ d) =>
  d a b ->
  c (Act f a) (Act f b)
map d = map_ @_ @_ @f d

-- The identity functor for some category k
data Id :: FUNCTOR k k

type instance Act Id x = x

instance Cat k => Functor (Id :: FUNCTOR k k) where
  map_ = id

-- Composing two compatible functors, is a functor
data (∘) :: FUNCTOR a b -> FUNCTOR x a -> FUNCTOR x b

type instance Act (f ∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f . map @g

-- The cross-product of two categories, is a category
data (×) :: CAT s -> CAT t -> CAT (s, t) where
  (:×:) :: l a b -> r x y -> (l × r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type IsPair :: (l, r) -> Constraint
type IsPair v = v ~ '(Fst v, Snd v)

type instance
  v ∈ (l × r) =
    Obj
      (l × r)
      ( IsPair v,
        Fst v ∈ l,
        Snd v ∈ r
      )

instance (Cat l, Cat r) => Cat (l × r) where
  identity = identity :×: identity
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

-- Every category has an opposite
data OP :: CAT i -> CAT i where
  OP :: k b a -> OP k a b

type instance i ∈ OP k = Obj (OP k) (i ∈ k)

instance Cat k => Cat (OP k) where
  identity = OP identity
  OP g ∘ OP f = OP (f ∘ g)

-- There's a category TYPE.
-- Whose objects are types,
-- and arrows are functions.
type TYPE = (->) :: CAT Type

type instance t ∈ TYPE = Obj TYPE (Known t)

instance Cat TYPE where
  identity = id
  (∘) = (.)

-- Some Yoneda embeddings

data Y :: forall (k :: CAT i) -> i -> FUNCTOR k TYPE

type instance Act (Y k d) c = k d c

instance (d ∈ k, Cat k) => Functor (Y k d) where
  map_ = (∘)

data K :: forall (k :: CAT i) -> i -> FUNCTOR (OP k) TYPE

type instance Act (K k c) d = k d c

instance (d ∈ k, Cat k) => Functor (K k d) where
  map_ (OP g) f = f ∘ g

data HOM :: forall (k :: CAT i) -> FUNCTOR (OP k × k) TYPE

type instance Act (HOM k) o = k (Fst o) (Snd o)

-- uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
-- instance Cat k => Functor (HOM k) where
--   map_ (f :×: g) t = f ∘ t ∘ g

-- Two functors f g may be adjoint when
--   `∀ a b. (a → g b) <=> (f a → b)`
-- Or in our notation:
--  `c a (Act g b) <=> d (Act f a) b`
type Adjoint :: FUNCTOR c d -> FUNCTOR d c -> Constraint
class
  (Functor f, Functor g) =>
  Adjoint f (g :: FUNCTOR d c)
    | f -> g,
      g -> f
  where
  leftAdjoint_ ::
    forall a b.
    ( a ∈ c,
      b ∈ d
    ) =>
    c a (Act g b) ->
    d (Act f a) b

  rightAdjoint_ ::
    forall a b.
    ( a ∈ c,
      b ∈ d
    ) =>
    d (Act f a) b ->
    c a (Act g b)

leftAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
    a ∈ c,
    b ∈ d
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjoint = leftAdjoint_ @c @d @f @g

rightAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
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
    (m :: ENDO c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘ f),
    Adjoint f g,
    a ∈ c
  ) =>
  c a (Act m a)
unit = rightAdjoint @f @g identity

counit ::
  forall
    {c}
    {d}
    (w :: ENDO d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘ g),
    Adjoint f g,
    a ∈ d
  ) =>
  d (Act w a) a
counit = leftAdjoint @f @g identity

join ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (m :: ENDO c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘ f),
    Adjoint f g,
    a ∈ c
  ) =>
  c (Act (m ∘ m) a) (Act m a)
join = do
  let t :: d (Act f (Act g (Act f a))) (Act f a)
      t = counit @(f ∘ g)
  map @g t

extend ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (w :: ENDO d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘ g),
    Adjoint f g,
    a ∈ d
  ) =>
  d (Act w a) (Act (w ∘ w) a)
extend = do
  let t :: c (Act g a) (Act g (Act f (Act g a)))
      t = unit @(g ∘ f)
  map @f t

-- Optics...

-- Lenses

type TYPEBifunctorObj k o = Obj k (IsPair o)

data DataLens :: CAT (Type, Type) where
  MkDataLens ::
    (s -> a) ->
    (s -> b -> t) ->
    DataLens '(a, b) '(s, t)

type instance o ∈ DataLens = TYPEBifunctorObj DataLens o

instance Cat DataLens where
  identity = MkDataLens id \_ -> id
  MkDataLens sa sbt ∘ MkDataLens ax ayb =
    MkDataLens (ax . sa) (\s -> sbt s . ayb (sa s))

type LensOn (p :: FUNCTOR DataLens TYPE) a b s t =
  forall {pab} {pst}.
  ( Functor p,
    '(a, b) ∈ DOM p,
    '(s, t) ∈ DOM p,
    pab ~ Act p '(a, b),
    pst ~ Act p '(s, t)
  ) =>
  pab ->
  pst

type Lens a b s t = forall p. Proxy p -> LensOn p a b s t

lens ::
  forall a b s t.
  (s -> a) ->
  (s -> b -> t) ->
  Lens a b s t
lens sa sbt = \(_ :: Proxy p) -> map @p (MkDataLens sa sbt)

first :: forall a b x. Lens a b (a, x) (b, x)
first = lens fst (\(_, x) b -> (b, x))

second :: forall a b x. Lens a b (x, a) (x, b)
second = lens snd (\(x, _) b -> (x, b))

-- Prisms

data DataPrism :: CAT (Type, Type) where
  MkDataPrism ::
    (s -> Either t a) ->
    (b -> t) ->
    DataPrism '(a, b) '(s, t)

type instance o ∈ DataPrism = TYPEBifunctorObj DataPrism o

instance Cat DataPrism where
  identity = MkDataPrism Right id
  MkDataPrism sta bt ∘ MkDataPrism abx yb =
    MkDataPrism
      (either Left (either (Left . bt) Right . abx) . sta)
      (bt . yb)

type PrismOn (p :: FUNCTOR DataPrism TYPE) a b s t =
  forall {pab} {pst}.
  ( Functor p,
    '(a, b) ∈ DOM p,
    '(s, t) ∈ DOM p,
    pab ~ Act p '(a, b),
    pst ~ Act p '(s, t)
  ) =>
  pab ->
  pst

type Prism a b s t = forall p. Proxy p -> PrismOn p a b s t

prism ::
  forall a b s t.
  (b -> t) ->
  (s -> Either t a) ->
  Prism a b s t
prism bt sta = \(_ :: Proxy p) -> map @p (MkDataPrism sta bt)

left :: forall a b x. Prism a b (Either a x) (Either b x)
left = prism Left \case
  Left a -> Right a
  Right x -> Left (Right x)

right :: forall a b x. Prism a b (Either x a) (Either x b)
right = prism Right \case
  Left x -> Left (Left x)
  Right a -> Right a

---

data READER :: Type -> FUNCTOR TYPE TYPE

type instance Act (READER x) y = x -> y

instance Functor (READER x) where
  map_ = (.)

data ENV :: Type -> FUNCTOR TYPE TYPE

type instance Act (ENV x) y = (x, y)

instance Functor (ENV x) where
  map_ f (l, r) = (l, f r)

data MONOID :: Type -> CAT () where
  MONOID :: m -> MONOID m '() '()

type instance
  x ∈ MONOID m =
    Obj
      (MONOID m)
      (x ~ '())

instance Monoid m => Cat (MONOID m) where
  identity = MONOID mempty
  MONOID l ∘ MONOID r = MONOID (l <> r)

data Δ :: forall (k :: CAT i) -> FUNCTOR k (k × k)

type instance Act (Δ k) x = '(x, x)

instance Cat k => Functor (Δ k) where
  map_ f = (f :×: f)

data (∧) :: FUNCTOR (TYPE × TYPE) TYPE

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map_ (f :×: g) (a, b) = (f a, g b)

data (∨) :: FUNCTOR (TYPE × TYPE) TYPE

type instance Act (∨) x = Either (Fst x) (Snd x)

instance Functor (∨) where
  map_ (f :×: g) = \case
    Left a -> Left (f a)
    Right b -> Right (g b)

instance Adjoint (Δ TYPE) (∧) where
  leftAdjoint_ t = (fst . t) :×: (snd . t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance Adjoint (∨) (Δ TYPE) where
  leftAdjoint_ (f :×: g) = f `either` g
  rightAdjoint_ t = (t . Left) :×: (t . Right)

flatMap ::
  forall
    {d :: CAT Type}
    (m :: ENDO TYPE)
    a
    b
    {f :: FUNCTOR TYPE d}
    {g :: FUNCTOR d TYPE}.
  ( m ~ (g ∘ f),
    Adjoint f g
  ) =>
  Act m a ->
  (a -> Act m b) ->
  Act m b
flatMap m t = join @m @b (map @m t m :: Act (m ∘ m) b)

type STATE s = READER s ∘ ENV s

instance Adjoint (ENV s) (READER s) where
  leftAdjoint_ asb (s, a) = asb a s
  rightAdjoint_ sab a s = sab (s, a)

type State s i = Act (STATE s) i

get :: State s s
get s = (s, s)

put :: s -> State s ()
put v _ = (v, ())

modify :: (s -> s) -> State s ()
modify t s = (t s, ())

newtype Bind m = Bind (forall a b. Act m a -> (a -> Act m b) -> Act m b)

newtype Pure m = Pure (forall a. a -> Act m a)

type MonadDo m = forall r. ((?bind :: Bind m, ?pure :: Pure m) => r) -> r

(>>=) :: forall m a b. (?bind :: Bind m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let Bind f = ?bind in f @a @b

pure :: forall m a. (?pure :: Pure m) => a -> Act m a
pure = let Pure u = ?pure in u

monadDo :: Bind m -> Pure m -> MonadDo m
monadDo b p t = do
  let ?bind = b
  let ?pure = p
  t

stateMonad :: MonadDo (STATE s)
stateMonad =
  monadDo
    (Bind (flatMap @(STATE _)))
    (Pure (unit @(STATE _)))

postinc :: State Int Int
postinc = stateMonad do
  x <- get
  _ <- put (x + 1)
  pure x

twicePostincShow :: State Int String
twicePostincShow = stateMonad do
  a <- postinc
  b <- postinc
  pure (show a <> "-" <> show b)

egState :: (Int, String)
egState = twicePostincShow 10

-- $> egState

-- f ∘ g ~> h
-- f ~> h / g
data (//) :: FUNCTOR d c -> FUNCTOR d d -> FUNCTOR c d

-- TODO - make more general
newtype Ran h g a = Ran (forall i. (a -> Act g i) -> Act h i)

type instance Act (h // g) x = Ran h g x

type CODENSITY f = f // f

-- f ~> g ∘ h
-- f \\ h ~> g
data (\\) :: FUNCTOR d c -> FUNCTOR d d -> FUNCTOR c d

-- TODO - make more general
data Lan f h a where
  (:\\:) :: Act f b -> (Act h b -> a) -> Lan f h a

main :: IO ()
main = putStrLn "main"
