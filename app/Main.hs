{-# LANGUAGE FlexibleContexts #-}
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
import Prelude hiding (Functor, map, pure, (>>=), product, succ, Monad, Monoid, Semigroup)
import qualified Prelude


{- Category: definition -}

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

type OBJECTS :: forall i. CATEGORY i -> Type
type OBJECTS (c :: CATEGORY i) = i

-- Type of functors indexed by domain & codomain categories
type (-->) :: forall i j. CATEGORY i -> CATEGORY j -> Type
type (-->) d c = Proxy d -> Proxy c -> Type

-- Project the domain category of a functor
type DOMAIN :: forall i (d :: CATEGORY i) c. (d --> c) -> CATEGORY i
type DOMAIN (f :: d --> c) = d

-- Project the codomain category of a functor
type CODOMAIN :: forall j d (c :: CATEGORY j). (d --> c) -> CATEGORY j
type CODOMAIN (f :: d --> c) = c

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


{- Category: Examples -}

-- "Equality" forms a category
data (:~:) :: CATEGORY t where
  Refl :: x :~: x

type instance (t :: k) ∈ (:~:) = Obj ((:~:) @k) (Known t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity = Refl


-- There's a category TYPE.
-- Whose objects are types,
-- and arrows are functions.
type TYPE = (->) :: CATEGORY Type

type instance t ∈ TYPE = Obj TYPE (Known t)

instance Semigroupoid TYPE where
  (∘) = (.)

instance Category TYPE where
  identity = id


-- Every category has an opposite
data OP :: CATEGORY i -> CATEGORY i where
  OP :: k b a -> OP k a b

type instance i ∈ OP k = Obj (OP k) (i ∈ k)

instance Semigroupoid k => Semigroupoid (OP k) where
  OP g ∘ OP f = OP (f ∘ g)

instance Category k => Category (OP k) where
  identity = OP identity


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


-- Natural numbers
data N = S N | Z

-- "Less than or equal to for Natural numbers" forms a category
data (≤) :: CATEGORY N where
  E :: n ≤ n
  B :: l ≤ u -> l ≤ 'S u

type TheN :: N -> N
type family TheN n where
  TheN 'Z = 'Z
  TheN ('S k) = 'S (TheN k)

type instance x ∈ (≤) =
  Obj
    (≤)
    (x ~ TheN x)

instance Semigroupoid (≤) where
  E ∘ r = r
  B l ∘ r = B (l ∘ r)

instance Category (≤) where
  identity = E


{- Monoid: definition -}

-- Monoids are categories with a single object
class (Category c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i)
instance (Category c, forall x y. (x ∈ c, y ∈ c) => x ~ y) => Monoid (c :: CATEGORY i)


{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: m -> PreludeMonoid m '() '()

type instance
  x ∈ PreludeMonoid m =
    Obj
      (PreludeMonoid m)
      (x ~ '())

instance Prelude.Semigroup m => Semigroupoid (PreludeMonoid m) where
  PreludeMonoid l ∘ PreludeMonoid r = PreludeMonoid (l <> r)

instance Prelude.Monoid m => Category (PreludeMonoid m) where
  identity = PreludeMonoid mempty


{- Functor: definition -}

-- Functors act on object names
type Act :: ((d :: CATEGORY i) --> (c :: CATEGORY j)) -> i -> j
type family Act f o

-- Type of evidence that `f` acting on `o` is an object in `f`'s codomain
class (Act f o ∈ CODOMAIN f) => Acts f o
instance (Act f o ∈ CODOMAIN f) => Acts f o

-- A functor is functorial for some object name.
-- If `o` is an object in `f`'s domain category,
-- then `f` acting on `o` is an object in `f`'s codomain category
type Functorial :: ((d :: CATEGORY o) --> c) -> o -> Constraint
type Functorial f o = (o ∈ DOMAIN f => Acts f o)

-- What is a functor?
-- Domain must be a category.
-- Codomain must be a category.
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
data Id :: forall k . k --> k

type instance Act Id x = x

instance Category k => Functor (Id :: k --> k) where
  map_ f = f

-- Composing two compatible functors, is a functor
data (∘) :: (a --> b) -> (x --> a) -> (x --> b)

type instance Act (f ∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f . map @g

-- Prelude.Functor is a specialisation of Functor
data PreludeFunctor f :: TYPE --> TYPE

type instance Act (PreludeFunctor f) a = f a

instance Prelude.Functor f => Functor (PreludeFunctor f) where
  map_ = fmap


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


-- Parallel functor coproduct

-- data (+++) :: (a --> s) -> (b --> t) -> ((a + b) --> (s + t))


-- Some Yoneda embeddings
data Y :: forall (k :: CATEGORY i) -> i -> (k --> TYPE)
type instance Act (Y k d) c = k d c
instance (d ∈ k, Category k) => Functor (Y k d) where
  map_ = (∘)

data L :: forall (k :: CATEGORY i) -> i -> (OP k --> TYPE)
type instance Act (L k c) d = k d c
instance (d ∈ k, Category k) => Functor (L k d) where
  map_ (OP g) f = f ∘ g

data HOM :: forall (k :: CATEGORY i) -> ((OP k × k) --> TYPE)
type instance Act (HOM k) o = k (Fst o) (Snd o)
instance Category k => Functor (HOM k) where
  map_ (OP f :×: g) t = g ∘ t ∘ f


{- Exponential category -}

data (^) :: forall c d -> CATEGORY (d --> c) where
  Exp ::
    (Functor f, Functor g) =>
    (forall i. i ∈ d => Proxy i -> c (Act f i) (Act g i)) ->
    (c ^ d) f g

unExp :: forall x c d i o . (x ∈ d) => (c ^ d) i o -> c (Act i x) (Act o x)
unExp (Exp f) = f (Proxy :: Proxy x)

type instance o ∈ (c ^ d) = Obj (c ^ d) (Functor o)

instance (Semigroupoid d, Semigroupoid c) => Semigroupoid (c ^ d) where
  l ∘ r = Exp \p -> case (l, r) of
    (Exp f, Exp g) -> (f p ∘ g p)

instance (Category d, Category c) => Category (c ^ d) where
  identity = Exp \_ -> identity


-- Functor composition is itself a functor
data FunctorCompose :: forall a b x . ((b ^ a) × (a ^ x)) --> (b ^ x)

type instance Act (FunctorCompose @a @b @x) e = Fst e ∘ Snd e

instance (Category a, Category b, Category x) => Functor (FunctorCompose @a @b @x) where
  -- map_ (Exp t :×: Exp s) = Exp \_ -> t Proxy ∘ s Proxy
  map_ _ = undefined


{- Adjunctions -}

-- Two functors f g may be adjoint when
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
    (m :: TYPE --> TYPE)
    a
    b
    {f :: TYPE --> d}
    {g :: d --> TYPE}.
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

-- ENV s ⊣ READER s

data READER :: Type -> (TYPE --> TYPE)

type instance Act (READER x) y = x -> y

instance Functor (READER x) where
  map_ = (.)

data ENV :: Type -> (TYPE --> TYPE)

type instance Act (ENV x) y = (y, x)

instance Functor (ENV x) where
  map_ f (l, r) = (f l, r)

instance ENV s ⊣ READER s where
  leftAdjoint_ = uncurry
  rightAdjoint_ = curry


-- (∨) ⊣ Δ TYPE ⊣ (∧)

data Δ :: forall (k :: CATEGORY i) -> (k --> (k × k))

type instance Act (Δ k) x = '(x, x)

instance Category k => Functor (Δ k) where
  map_ f = (f :×: f)

data (∧) :: (TYPE × TYPE) --> TYPE

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  map_ (f :×: g) (a, b) = (f a, g b)

data (∨) :: (TYPE × TYPE) --> TYPE

type instance Act (∨) x = Either (Fst x) (Snd x)

instance Functor (∨) where
  map_ (f :×: g) = either (Left . f) (Right . g)

instance Δ TYPE ⊣ (∧) where
  leftAdjoint_ t = (fst . t) :×: (snd . t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ TYPE where
  leftAdjoint_ (f :×: g) = f `either` g
  rightAdjoint_ t = (t . Left) :×: (t . Right)


-- Monad
-- Works but using the class crashes the compiler
{-
type DeCompMidIx :: (c --> c) -> Type
type family DeCompMidIx m where
  DeCompMidIx (g ∘ f) = OBJECTS (CODOMAIN f)

type DeCompMid :: forall (m :: c --> c) -> CATEGORY (DeCompMidIx m)
type family DeCompMid m where
  DeCompMid (g ∘ f) = CODOMAIN f

type Outer :: forall (m :: c --> c) -> (DeCompMid m --> c)
type family Outer m where
  Outer (g ∘ f) = g

type Inner :: forall (m :: c --> c) -> (c --> DeCompMid m)
type family Inner m where
  Inner (g ∘ f) = f

type Decomposed :: (c --> c) -> (c --> c)
type Decomposed m = Outer m ∘ Inner m

class (m ~ Decomposed m, Inner m ⊣ Outer m) => Monad m
instance (m ~ Decomposed m, Inner m ⊣ Outer m) => Monad m
-}


-- Other crap

data DISCRETE :: forall t -> CATEGORY t where DISCRETE :: DISCRETE t b b
type instance i ∈ DISCRETE t = Obj (DISCRETE t) (Known i)
instance Semigroupoid (DISCRETE t) where DISCRETE ∘ DISCRETE = DISCRETE
instance Category (DISCRETE t) where identity = DISCRETE

data CONST :: i -> (d --> (c :: CATEGORY i))
type instance Act (CONST x) o = x
instance (Category d, Category c, x ∈ c) => Functor (CONST x :: d --> c) where
  map_ _ = identity

data (∆) :: forall j (k :: CATEGORY i) -> (k --> (k ^ j))
type instance Act ((∆) j k) o = CONST o
instance (Category j, Category k) => Functor ((∆) j k) where
  map_ t = Exp \_ -> t

type DELTA k = (∆) (DISCRETE Bool) k

data PARTIAL :: (((l :: CATEGORY i) × r) --> k) -> i -> (r --> k)
type instance Act (PARTIAL f x) y = Act f '(x, y)
instance
  ( Category l, Category r, Category k, Functor f, x ∈ l
  ) => Functor (PARTIAL (f :: (l × r) --> k) x) where
    map_ rab = map @f (identity @_ @_ @x :×: rab)

data CURRY :: ((l × r) --> k) -> (l --> (k ^ r))
type instance Act (CURRY f) o = PARTIAL f o
instance (Category l, Category r, Category k, Functor f) => Functor (CURRY f :: l --> (k ^ r)) where
  map_ lab = Exp \(_ :: Proxy z) -> map @f (lab :×: identity @_ @r @z)

-- Uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
data UNCURRY :: (l --> (k ^ r)) -> ((l × r) --> k)
type instance Act (UNCURRY f) o = Act (Act f (Fst o)) (Snd o)
-- class Functor (Act f i) => FunctorAct f i
-- instance Functor (Act f i) => FunctorAct f i
-- instance (Category l, Category r, Category k, Functor f, forall i . i ∈ l => FunctorAct f i) => Functor (UNCURRY f :: (l × r) --> k) where
--   map_ (l :×: r) = map @r r ∘ Exp \(_ :: Proxy z) -> map @(Act f z) (l :×: identity)

-- Finite sets
data Fin :: N -> Type where
  FS :: Fin k -> Fin ('S k)
  FZ :: Fin ('S n)

-- Singleton for finite sets
data SFin :: forall n -> Fin n -> Type where
  SFS :: SFin n k -> SFin ('S n) ('FS k)
  SFZ :: SFin ('S n) 'FZ

data Vect :: N -> Type -> Type where
  Nil :: Vect 'Z t
  Cons :: t -> Vect n t -> Vect ('S n) t

data VECT :: ((:~:) @N × TYPE) --> TYPE
type instance Act VECT x = Vect (Fst x) (Snd x)
instance Functor VECT where
  map_ (Refl :×: g) = \case
    Nil -> Nil
    Cons h t -> Cons (g h) (map @VECT (Refl :×: g) t)

-- A tuple is a pi type like: `(f : Fin n) → o f` for some functor `o` from the
-- discrete category of finite sets to the category of types and functions.
-- We encode this using a polymorphic function from a singleton finite set.
data Tuple :: (DISCRETE (Fin n) --> TYPE) -> Type where
  Tuple :: (forall f . SFin n f -> Act o f) -> Tuple o

data FINITE :: forall n -> (TYPE ^ DISCRETE (Fin n)) --> TYPE
type instance Act (FINITE n) o = Tuple o
instance Functor (FINITE n) where
  map_ (Exp t) (Tuple s) = Tuple \(g :: SFin n f) -> t (Proxy @f) (s g)


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

monadDo :: BindDo m -> PureDo m -> MonadDo m
monadDo b p t = do
  let ?bind = b
  let ?pure = p
  t

makeBind ::
  forall (m :: TYPE --> TYPE) {f} {g}.
  (m ~ (g ∘ f), f ⊣ g) =>
  BindDo m
makeBind = BindDo (flatMap @m)

makePure ::
  forall (m :: TYPE --> TYPE) {f} {g}.
  (m ~ (g ∘ f), f ⊣ g) =>
  PureDo m
makePure = PureDo (unit @m)

-- makeMonadDo ::
--   forall (m :: TYPE --> TYPE) {f} {g}.
--   (m ~ (g ∘ f), f ⊣ g) =>
--   MonadDo m
-- makeMonadDo =
--   monadDo
--     (makeBind @m)
--     (makePure @m)

---

type MONOID_OBJECT :: forall i . CATEGORY i -> i -> Type
type MONOID_OBJECT k e = Proxy k -> Proxy e -> Type

class
  Functor (Two n :: (k × k) --> k) =>
  MonoidObject (n :: MONOID_OBJECT @i k e) where
    type Zero (n :: MONOID_OBJECT @i k e) :: i
    type Two (n :: MONOID_OBJECT @i k e) :: (k × k) --> k
    moEmpty :: (Zero n ∈ k, e ∈ k) => k (Zero n) e
    moAppend :: (e ∈ k) => k (Act (Two n) '( e, e )) e

data RegularMonoid :: forall m -> MONOID_OBJECT TYPE m

instance Prelude.Monoid m => MonoidObject (RegularMonoid m) where
  type Zero (RegularMonoid m) = ()
  type Two (RegularMonoid m) = (∧)
  moEmpty _ = mempty
  moAppend (l, r) = l <> r

-- monads are monoid objects in the category of endofunctors
data MAMOITCOE :: forall k m -> MONOID_OBJECT (k ^ k) m

instance
  (m ~ (g ∘ f), f ⊣ g) =>
  MonoidObject (MAMOITCOE k m) where
    type Zero (MAMOITCOE k m) = Id @k
    type Two (MAMOITCOE k m) = FunctorCompose @k @k @k

    moEmpty :: (k ^ k) Id m
    moEmpty = Exp (\_ -> unit @(g ∘ f))

    moAppend :: (k ^ k) (m ∘ m) m
    moAppend = Exp (\(Proxy @_ @a) -> join @m @a)

type Dup = (∧) ∘ Δ TYPE

dupMonad :: MonadDo Dup
dupMonad =
  monadDo
    (makeBind @Dup)
    (makePure @Dup)

egDuped :: (Int, Int)
egDuped = dupMonad do
  v <- (10, 100)
  x <- (v + 1, v + 2)
  pure (x * 2)

-- $> egDuped -- (22,204)

type STATE s = READER s ∘ ENV s

stateMonad :: MonadDo (STATE s)
stateMonad =
  monadDo
    (makeBind @(STATE _))
    (makePure @(STATE _))

type State s i = Act (STATE s) i

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
  pure (show a <> "-" <> show b <> "-" <> show c)

egState :: (String, Int)
egState = twicePostincShow 10

-- $> egState

data Free t a = Free
  { runFree ::
      forall m {f} {g}.
      (m ~ (g ∘ f), f ⊣ g) =>
      (forall i. Act t i -> Act m i) ->
      Act m a
  }

data FREE :: (k --> k) -> (k --> k)

-- COEND
-- DAY
-- f ★ g

-- f ∘ g ~> h
-- f ~> h / g
data (//) :: (d --> c) -> (d --> d) -> (c --> d)

-- TODO - make more general
newtype Ran h g a = Ran (forall i. (a -> Act g i) -> Act h i)

type instance Act (h // g) x = Ran h g x

type CODENSITY f = f // f

-- f ~> g ∘ h
-- f \\ h ~> g
data (\\) :: (d --> c) -> (d --> d) -> (c --> d)

-- TODO - make more general
data Lan f h a where
  (:\\:) :: Act f b -> (Act h b -> a) -> Lan f h a

{-

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

type LensOn (p :: DataLens --> TYPE) a b s t =
  forall {pab} {pst}.
  ( Functor p,
    '(a, b) ∈ DOMAIN p,
    '(s, t) ∈ DOMAIN p,
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

type PrismOn (p :: DataPrism --> TYPE) a b s t =
  forall {pab} {pst}.
  ( Functor p,
    '(a, b) ∈ DOMAIN p,
    '(s, t) ∈ DOMAIN p,
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

-}

type (&) :: i -> i -> CATEGORY i -> i
type family (&) l r k

class ((a & b) k ∈ k) => CartesianActs k a b

instance ((a & b) k ∈ k) => CartesianActs k a b

type CartesianFunctorial :: CATEGORY o -> o -> o -> Constraint
type CartesianFunctorial k a b = ((a ∈ k, b ∈ k) => CartesianActs k a b)

class
  ( Category k,
    forall a b. CartesianFunctorial k a b
  ) =>
  Cartesian k
  where
  product :: (i ∈ k, a ∈ k, b ∈ k) => k i a -> k i b -> k i ((a & b) k)
  first :: (l ∈ k, r ∈ k) => k ((l & r) k) l
  second :: (l ∈ k, r ∈ k) => k ((l & r) k) r

type instance (l & r) TYPE = (l, r)

instance Cartesian TYPE where
  product l r i = (l i, r i)
  first (l, _) = l
  second (_, r) = r

data (&&&&) :: (d × d) --> d
type instance Act ((&&&&) :: (d × d) --> d) o = (Fst o & Snd o) d
-- Uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
-- instance Cartesian d => Functor ((&&&&) :: (d × d) --> d) where
--   map_ (l :×: r) = (l ∘ first) `product` (r ∘ second)

type Acting :: ((d :: CATEGORY o) --> TYPE) -> o -> Type
data Acting f a = Acting (Act f a)

data Day :: ((d :: CATEGORY i) --> TYPE) -> (d --> TYPE) -> i -> Type where
  MkDay ::
    (a ∈ d, b ∈ d, c ∈ d) =>
    Acting (f :: d --> TYPE) a ->
    Acting (g :: d --> TYPE) b ->
    d ((a & b) d) c ->
    Day f g c

data DAY :: (d --> TYPE) -> (d --> TYPE) -> (d --> TYPE)

type instance Act (DAY f g) c = Day f g c

instance
  ( Functor f,
    Functor g,
    Cartesian d
  ) =>
  Functor (DAY f g :: d --> TYPE)
  where
  map_ d (MkDay f g c) = MkDay f g (d ∘ c)

---

type Terminal :: CATEGORY i -> i
type family Terminal k
class (Category k, Terminal k ∈ k) => HasTerminal k where
  term :: k i (Terminal k)

type instance Terminal TYPE = ()
instance HasTerminal TYPE where
  term _ = ()

---

main :: IO ()
main = putStrLn ""
