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
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Kind
import Data.Proxy
import Prelude hiding (Functor, map, pure, (>>=))

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Type of functors indexed by domain & codomain categories
type FUNCTOR :: forall i j. CATEGORY i -> CATEGORY j -> Type
type FUNCTOR d c = Proxy d -> Proxy c -> Type

-- Endofunctors domain & codomain categories are the same
type ENDO :: CATEGORY i -> Type
type ENDO k = FUNCTOR k k

-- Project the domain category of a functor
type DOM :: forall i (d :: CATEGORY i) c. FUNCTOR d c -> CATEGORY i
type DOM (f :: FUNCTOR d c) = d

-- Project the codomain category of a functor
type COD :: forall j d (c :: CATEGORY j). FUNCTOR d c -> CATEGORY j
type COD (f :: FUNCTOR d c) = c

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k = o | o -> k x

type Known :: t -> Constraint
type Known t = t ~ t

-- Helper to deal with injectivity when instancing ∈
type Obj :: CATEGORY i -> Constraint -> Constraint
type Obj k c = (Known k, c)

-- What is a category
type Semigroupoid :: CATEGORY i -> Constraint
class Semigroupoid k where
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

-- What is a category
type Category :: CATEGORY i -> Constraint
class Semigroupoid k => Category k where
  identity :: i ∈ k => k i i

-- Functors act on object names
type Act :: FUNCTOR (d :: CATEGORY i) (c :: CATEGORY j) -> i -> j
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ COD f) => Acts f o

instance (Act f o ∈ COD f) => Acts f o

-- A functor is functorial for some object name.
-- If `o` is an object in `f`'s domain category,
-- then `f` acting on `o` is an object in `f`'s codomain category
type Functorial :: FUNCTOR (d :: CATEGORY o) c -> o -> Constraint
type Functorial f o = (o ∈ DOM f => Acts f o)

-- What is a functor?
-- Domain must be a category.
-- Codomain must be a category.
-- `f` must be functorial for all possible object names.
-- Also arrows can be mapped.
type Functor :: FUNCTOR d c -> Constraint
class (Category d, Category c, forall o. Functorial f o) => Functor (f :: FUNCTOR d c) where
  map_ :: (a ∈ d, b ∈ d) => d a b -> c (Act f a) (Act f b)

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

instance Category k => Functor (Id :: FUNCTOR k k) where
  map_ = id

-- Composing two compatible functors, is a functor
data (∘) :: FUNCTOR a b -> FUNCTOR x a -> FUNCTOR x b

type instance Act (f ∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f . map @g

-- The cross-product of two categories, is a category
data (×) :: CATEGORY s -> CATEGORY t -> CATEGORY (s, t) where
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

instance (Semigroupoid l, Semigroupoid r) => Semigroupoid (l × r) where
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

instance (Category l, Category r) => Category (l × r) where
  identity = identity :×: identity

-- Every category has an opposite
data OP :: CATEGORY i -> CATEGORY i where
  OP :: k b a -> OP k a b

type instance i ∈ OP k = Obj (OP k) (i ∈ k)

instance Semigroupoid k => Semigroupoid (OP k) where
  OP g ∘ OP f = OP (f ∘ g)

instance Category k => Category (OP k) where
  identity = OP identity

-- There's a category TYPE.
-- Whose objects are types,
-- and arrows are functions.
type TYPE = (->) :: CATEGORY Type

type instance t ∈ TYPE = Obj TYPE (Known t)

instance Semigroupoid TYPE where
  (∘) = (.)

instance Category TYPE where
  identity = id

-- Some Yoneda embeddings

data Y :: forall (k :: CATEGORY i) -> i -> FUNCTOR k TYPE

type instance Act (Y k d) c = k d c

instance (d ∈ k, Category k) => Functor (Y k d) where
  map_ = (∘)

data L :: forall (k :: CATEGORY i) -> i -> FUNCTOR (OP k) TYPE

type instance Act (L k c) d = k d c

instance (d ∈ k, Category k) => Functor (L k d) where
  map_ (OP g) f = f ∘ g

data HOM :: forall (k :: CATEGORY i) -> FUNCTOR (OP k × k) TYPE

type instance Act (HOM k) o = k (Fst o) (Snd o)

-- Uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
-- instance Category k => Functor (HOM k) where
--   map_ (f :×: g) t = f ∘ t ∘ g

data (^) :: forall c d -> CATEGORY (FUNCTOR d c) where
  Exp ::
    (Functor f, Functor g) =>
    (forall i. i ∈ d => Proxy i -> c (Act f i) (Act g i)) ->
    (c ^ d) f g

type instance
  o ∈ (c ^ d) =
    Obj (c ^ d) (Functor o)

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = Exp \p -> case (l, r) of
    (Exp f, Exp g) -> (f p ∘ g p)

instance (Category d, Category c) => Category (c ^ d) where
  identity = Exp \_ -> identity

data DISCRETE :: forall t -> CATEGORY t where DISCRETE :: DISCRETE t b b
type instance i ∈ DISCRETE t = Obj (DISCRETE t) (Known i)
instance Semigroupoid (DISCRETE t) where DISCRETE ∘ DISCRETE = DISCRETE
instance Category (DISCRETE t) where identity = DISCRETE

data CONST :: i -> FUNCTOR d (c :: CATEGORY i)
type instance Act (CONST x) o = x
instance (Category d, Category c, x ∈ c) => Functor (CONST x :: FUNCTOR d c) where map_ _ = identity

data Δ :: forall j (k :: CATEGORY i) -> FUNCTOR k (k ^ j)
type instance Act (Δ j k) o = CONST o
instance (Category j, Category k) => Functor (Δ j k) where
  map_ t = Exp \_ -> t

type DELTA k = Δ (DISCRETE Bool) k

data PARTIAL :: FUNCTOR ((l :: CATEGORY i) × r) k -> i -> FUNCTOR r k
type instance Act (PARTIAL f x) y = Act f '(x, y)
instance (Category l, Category r, Category k, Functor f, x ∈ l) => Functor (PARTIAL (f :: FUNCTOR (l × r) k) x) where
  map_ rab = map @f (identity @_ @_ @x :×: rab)

data CURRY :: FUNCTOR (l × r) k -> FUNCTOR l (k ^ r)
type instance Act (CURRY f) o = PARTIAL f o
instance (Category l, Category r, Category k, Functor f) => Functor (CURRY f :: FUNCTOR l (k ^ r)) where
  map_ lab = Exp \(_ :: Proxy z) -> map @f (lab :×: identity @_ @r @z)

-- Uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
-- data UNCURRY :: FUNCTOR l (k ^ r) -> FUNCTOR (l × r) k
-- type instance Act (UNCURRY f) o = Act (Act f (Fst o)) (Snd o)
-- instance (Category l, Category r, Category k, Functor f) => Functor (UNCURRY f :: FUNCTOR (l × r) k) where
--   map_ lab = Exp \(_ :: Proxy z) -> map @f (lab :×: identity @_ @_ @z)

-- Natural numbers
data N = S N | Z

-- Finite sets
data Fin :: N -> Type where
  FS :: Fin k -> Fin ('S k)
  FZ :: Fin ('S n)

-- Singleton for finite sets
data SFin :: forall n -> Fin n -> Type where
  SFS :: SFin n k -> SFin ('S n) ('FS k)
  SFZ :: SFin ('S n) 'FZ

-- A tuple is a pi type like: `(f : Fin n) → o f` for some functor `o` from the
-- discrete category of finite sets to the category of types and functions.
-- We encode this using a polymorphic function from a singleton finite set.
data Tuple :: FUNCTOR (DISCRETE (Fin n)) TYPE -> Type where
  Tuple :: (forall f . SFin n f -> Act o f) -> Tuple o

-- Example tuple
type Three = 'S ('S ('S 'Z))
data RRR :: FUNCTOR (DISCRETE (Fin Three)) TYPE
type instance Act RRR 'FZ = Int
type instance Act RRR ('FS 'FZ) = String
type instance Act RRR ('FS ('FS 'FZ)) = Bool
egTuple :: Tuple RRR
egTuple = Tuple \case
  SFZ -> 4
  SFS SFZ -> "Hi"
  SFS (SFS SFZ) -> True

data FINITE :: forall n -> FUNCTOR (TYPE ^ DISCRETE (Fin n)) TYPE
type instance Act (FINITE n) o = Tuple o
instance Functor (FINITE n) where
  map_ (Exp t) (Tuple s) = Tuple \(g :: SFin n f) -> t (Proxy @f) (s g)

-- Two functors f g may be adjoint when
--   `∀ a b. (a → g b) <=> (f a → b)`
-- Or in our notation:
--   `∀ a b . c a (Act g b) <=> d (Act f a) b`
type (⊣) :: FUNCTOR c d -> FUNCTOR d c -> Constraint
class (Functor f, Functor g) => f ⊣ (g :: FUNCTOR d c) | f -> g, g -> f where
  leftAdjoint_ :: forall a b. (a ∈ c, b ∈ d) => c a (Act g b) -> d (Act f a) b
  rightAdjoint_ :: forall a b. (a ∈ c, b ∈ d) => d (Act f a) b -> c a (Act g b)

leftAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( f ⊣ g,
    a ∈ c,
    b ∈ d
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjoint = leftAdjoint_ @c @d @f @g

rightAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
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
    (m :: ENDO c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
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
    (w :: ENDO d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
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
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    (m :: ENDO c)
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
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    (w :: ENDO d)
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
  forall {d} (m :: ENDO TYPE) a b {f :: FUNCTOR TYPE d} {g :: FUNCTOR d TYPE}.
  (m ~ (g ∘ f), f ⊣ g) =>
  Act m a ->
  (a -> Act m b) ->
  Act m b
flatMap m t = join @m @b (map @m t m :: Act (m ∘ m) b)

newtype BindDo m = BindDo (forall a b. Act m a -> (a -> Act m b) -> Act m b)

newtype PureDo m = PureDo (forall a. a -> Act m a)

type MonadDo m = forall r. ((?bind :: BindDo m, ?pure :: PureDo m) => r) -> r

(>>=) :: forall m a b. (?bind :: BindDo m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let BindDo f = ?bind in f @a @b

pure :: forall m a. (?pure :: PureDo m) => a -> Act m a
pure = let PureDo u = ?pure in u

monadDo :: BindDo m -> PureDo m -> MonadDo m
monadDo b p t = do
  let ?bind = b
  let ?pure = p
  t

-- hmmmmmm how to make this type check???
-- makeBind ::
--   forall (m :: ENDO TYPE) {f} {g}.
--   (m ~ (g ∘ f), f ⊣ g) =>
--   BindDo m
-- makeBind = BindDo (flatMap @m)

makePure ::
  forall (m :: ENDO TYPE) {f} {g}.
  (m ~ (g ∘ f), f ⊣ g) =>
  PureDo m
makePure = PureDo (unit @m)

-- makeMonadDo ::
--   forall (m :: ENDO TYPE) {f} {g}.
--   (m ~ (g ∘ f), f ⊣ g) =>
--   MonadDo m
-- makeMonadDo = monadDo makeBind makePure

---

data MONOID :: Type -> CATEGORY () where
  MONOID :: m -> MONOID m '() '()

type instance
  x ∈ MONOID m =
    Obj
      (MONOID m)
      (x ~ '())

instance Semigroup m => Semigroupoid (MONOID m) where
  MONOID l ∘ MONOID r = MONOID (l <> r)

instance Monoid m => Category (MONOID m) where
  identity = MONOID mempty

data READER :: Type -> FUNCTOR TYPE TYPE

type instance Act (READER x) y = x -> y

instance Functor (READER x) where
  map_ = (.)

data ENV :: Type -> FUNCTOR TYPE TYPE

type instance Act (ENV x) y = (y, x)

instance Functor (ENV x) where
  map_ f (l, r) = (f l, r)

instance ENV s ⊣ READER s where
  leftAdjoint_ = uncurry
  rightAdjoint_ = curry

data K :: forall (k :: CATEGORY i) -> FUNCTOR k (k × k)

type instance Act (K k) x = '(x, x)

instance Category k => Functor (K k) where
  map_ f = (f :×: f)

data (∧) :: FUNCTOR (TYPE × TYPE) TYPE

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map_ (f :×: g) (a, b) = (f a, g b)

data (∧∧) :: FUNCTOR (TYPE ^ DISCRETE Bool) TYPE

type instance Act (∧∧) o = (Act o 'False, Act o 'True)

instance Functor (∧∧) where
  map_ (Exp t) (a, b) =
    (t (Proxy @'False) a, t (Proxy @'True) b)

data (∨) :: FUNCTOR (TYPE × TYPE) TYPE

type instance Act (∨) x = Either (Fst x) (Snd x)

instance Functor (∨) where
  map_ (f :×: g) = either (Left . f) (Right . g)

instance K TYPE ⊣ (∧) where
  leftAdjoint_ t = (fst . t) :×: (snd . t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ K TYPE where
  leftAdjoint_ (f :×: g) = f `either` g
  rightAdjoint_ t = (t . Left) :×: (t . Right)

type Dup = (∧) ∘ K TYPE

dupMonad :: MonadDo Dup
dupMonad =
  monadDo
    (BindDo (flatMap @Dup))
    (PureDo (unit @Dup))

egDuped :: (Int, Int)
egDuped = dupMonad do
  v <- (10, 100)
  x <- (v + 1, v + 2)
  pure (x * 2)

-- $> egDuped -- (22,204)

type STATE s = READER s ∘ ENV s

type State s i = Act (STATE s) i

get :: State s s
get s = (s, s)

put :: s -> State s ()
put v _ = ((), v)

modify :: (s -> s) -> State s ()
modify t s = ((), t s)

stateMonad :: MonadDo (STATE s)
stateMonad =
  monadDo
    (BindDo (flatMap @(STATE _)))
    (PureDo (unit @(STATE _)))

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

egState :: (String, Int)
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

-- Optics...

-- Lenses

type TYPEBifunctorObj k o = Obj k (IsPair o)

data DataLens :: CATEGORY (Type, Type) where
  MkDataLens ::
    (s -> a) ->
    (s -> b -> t) ->
    DataLens '(a, b) '(s, t)

type instance o ∈ DataLens = TYPEBifunctorObj DataLens o

instance Semigroupoid DataLens where
  MkDataLens sa sbt ∘ MkDataLens ax ayb =
    MkDataLens (ax . sa) (\s -> sbt s . ayb (sa s))

instance Category DataLens where
  identity = MkDataLens id \_ -> id

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

data DataPrism :: CATEGORY (Type, Type) where
  MkDataPrism ::
    (s -> Either t a) ->
    (b -> t) ->
    DataPrism '(a, b) '(s, t)

type instance o ∈ DataPrism = TYPEBifunctorObj DataPrism o

instance Semigroupoid DataPrism where
  MkDataPrism sta bt ∘ MkDataPrism abx yb =
    MkDataPrism
      (either Left (either (Left . bt) Right . abx) . sta)
      (bt . yb)

instance Category DataPrism where
  identity = MkDataPrism Right id

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

main :: IO ()
main = putStrLn (show egState)
