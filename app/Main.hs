{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
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
import Prelude hiding
  ( Foldable,
    Functor,
    Monad,
    Monoid,
    Semigroup,
    foldMap,
    map,
    product,
    pure,
    succ,
    (>>=),
  )
import qualified Prelude

{- Category: definition -}

-- Type of categories represented by their hom-types indexed by object names
type CATEGORY :: Type -> Type
type CATEGORY i = i -> i -> Type

-- Lookup the type of a category's object names
type NAMES :: forall i. CATEGORY i -> Type
type NAMES (c :: CATEGORY i) = i

-- Categories must specify what it means to be an object in that category
type (∈) :: forall i. i -> CATEGORY i -> Constraint
type family x ∈ k

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

type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  Refl ∘ Refl = Refl

instance Category (:~:) where
  identity = Refl

-- There's a category TYPE.
-- Whose objects are types,
-- and arrows are functions.
type TYPE = (->) :: CATEGORY Type

type instance t ∈ TYPE = (t ~ t)

instance Semigroupoid TYPE where
  (∘) = (.)

instance Category TYPE where
  identity = id

-- Every category has an opposite
data OP :: CATEGORY i -> CATEGORY i where
  OP :: k b a -> OP k a b

type instance i ∈ OP k = i ∈ k

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
  identity = PreludeMonoid mempty

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
type DOMAIN :: forall i (d :: CATEGORY i) c. (d --> c) -> CATEGORY i
type DOMAIN (f :: d --> c) = d

-- Project the codomain category of a functor
type CODOMAIN :: forall j d (c :: CATEGORY j). (d --> c) -> CATEGORY j
type CODOMAIN (f :: d --> c) = c

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

-- Foldable?

class Foldable t where
  foldMap :: (Monoid c o) => (a -> c o o) -> Act t a -> c o o

data List :: TYPE --> TYPE

type instance Act List t = [t]

instance Functor List where
  map_ = fmap

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

-- (∘ g) ⊣ (/ g)
-- aka (PostCompose g ⊣ PostRan g)

data PostCompose :: (c --> c') -> (a ^ c') --> (a ^ c)

type instance Act (PostCompose g) f = f ∘ g

instance
  (Category c, Category c', Category a, Functor g) =>
  Functor (PostCompose @c @c' @a g)
  where
  map_ (Exp h) = Exp \(Proxy :: Proxy i) -> h (Proxy @(Act g i))

type Ran :: (x --> TYPE) -> (x --> z) -> NAMES z -> Type
data Ran h g a where
  Ran ::
    Functor f =>
    Proxy f ->
    ((f ∘ g) ~> h) ->
    Act f a ->
    Ran h g a

-- NOTE: currently y is always TYPE
data (/) :: (x --> y) -> (x --> z) -> (z --> y)

type instance Act (h / g) o = Ran h g o

instance (Category x, Category z) => Functor ((/) @x @TYPE @z h g) where
  map_ zab (Ran (pf :: Proxy f) fgh fa) =
    Ran pf fgh (map @f zab fa)

-- NOTE: currently y is always TYPE
data PostRan :: (x --> z) -> (y ^ x) --> (y ^ z)

type instance Act (PostRan g) h = h / g

instance
  (Category x, Category z, Functor g) =>
  Functor (PostRan @x @z @TYPE g)
  where
  map_ ab =
    Exp \_ (Ran p fga fi) ->
      Ran p (ab ∘ fga) fi

instance (Functor g) => PostCompose g ⊣ PostRan @x @z @TYPE g where
  leftAdjoint_ a_bg =
    Exp \(Proxy :: Proxy i) ag ->
      case runExp @(Act g i) a_bg ag of
        Ran _ fg_b fgi ->
          runExp @i fg_b fgi

  rightAdjoint_ ag_b =
    Exp \(Proxy :: Proxy i) (a :: Act a i) ->
      Ran (Proxy @a) ag_b a

type CODENSITY :: (x --> TYPE) -> (TYPE --> TYPE)
type CODENSITY f = f / f

-- Monad
-- "Works" but using the class crashes the compiler
{-
type DeCompMidIx :: (c --> c) -> Type
type family DeCompMidIx m where
  DeCompMidIx (g ∘ f) = NAMES (CODOMAIN f)

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
      Proxy m ->
      Proxy a ->
      (t ~> m) ->
      Act (g ∘ f) a
  }

data FREE0 :: (k --> k) -> (k --> k)

data FREE1 :: (k ^ k) --> (k ^ k)

type instance Act (FREE0 f) o = Free f o

type instance Act FREE1 f = FREE0 f

instance Functor (FREE0 @TYPE t) where
  map_ = undefined

-- map_ (a_b :: a -> b) (Free f) =
-- Free \(m :: Proxy m) (Proxy :: Proxy b) (t_m :: t ~> m) ->
--   map @m a_b (f m (Proxy @a) t_m)

instance Functor (FREE1 @TYPE) where
  map_ = undefined

---

main :: IO ()
main = putStrLn ""
