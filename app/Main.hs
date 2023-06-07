{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Foldable qualified as Foldable
import Data.Kind
import Data.Proxy
import Defs
import Prelude (fromInteger, ($))
import Prelude qualified

{- Category: Examples -}

-- "Equality" forms a category
data (:~:) :: CATEGORY t where
  REFL :: x :~: x

type instance (t :: k) ∈ (:~:) = (t ~ t)

instance Semigroupoid (:~:) where
  REFL ∘ REFL = REFL

instance Category (:~:) where
  identity_ = REFL

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
  identity_ = E

{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: {getPreludeMonoid :: m} -> PreludeMonoid m '() '()

type instance x ∈ PreludeMonoid m = (x ~ '())

instance Prelude.Semigroup m => Semigroupoid (PreludeMonoid m) where
  PreludeMonoid l ∘ PreludeMonoid r = PreludeMonoid (l Prelude.<> r)

instance Prelude.Monoid m => Category (PreludeMonoid m) where
  identity_ = PreludeMonoid Prelude.mempty

boring_monoid_category_example :: ()
boring_monoid_category_example = ()
  where
    _monoid_mappend :: Monoid c o => c o o -> c o o -> c o o
    _monoid_mappend = (∘)

    _monoid_mempty :: Monoid c o => c o o
    _monoid_mempty = identity

    _eg0 :: [Prelude.Integer]
    _eg0 = getPreludeMonoid _monoid_mempty

    _eg1 :: [Prelude.Integer]
    _eg1 = getPreludeMonoid $ PreludeMonoid [1] `_monoid_mappend` PreludeMonoid [2, 3]

data Endo :: i -> CATEGORY i -> CATEGORY () where
  ENDO :: c o o -> Endo o c '() '()

type instance x ∈ Endo o c = (x ~ '())

instance (Semigroupoid c, o ∈ c) => Semigroupoid (Endo o c) where
  ENDO l ∘ ENDO r = ENDO (l ∘ r)

instance (Category c, o ∈ c) => Category (Endo o c) where
  identity_ = ENDO identity

{- Functor: examples -}

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
  map_ (OP g) f = f ∘ g

data Hom :: forall (k :: CATEGORY i) -> ((Op k × k) --> Types)

type instance Act (Hom k) o = k (Fst o) (Snd o)

instance Category k => Functor (Hom k) where
  map_ (OP f :×: g) t = g ∘ t ∘ f

{- Adjunctions: examples -}

-- Env s ⊣ Reader s

data Reader :: Type -> (Types --> Types)

type instance Act (Reader x) y = x -> y

instance Functor (Reader x) where
  map_ = (∘)

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

type instance Act (∨) x = Prelude.Either (Fst x) (Snd x)

instance Functor (∨) where
  map_ (f :×: g) = Prelude.either (Prelude.Left ∘ f) (Prelude.Right ∘ g)

instance Δ Types ⊣ (∧) where
  leftAdjoint_ t = (Prelude.fst ∘ t) :×: (Prelude.snd ∘ t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance (∨) ⊣ Δ Types where
  leftAdjoint_ (f :×: g) = f `Prelude.either` g
  rightAdjoint_ t = (t ∘ Prelude.Left) :×: (t ∘ Prelude.Right)

-- (∘ g) ⊣ (/ g)
-- aka (PostCompose g ⊣ PostRan g)

data PostCompose :: (c --> c') -> (a ^ c') --> (a ^ c)

type instance Act (PostCompose g) f = f ∘ g

instance
  (Category c, Category c', Category a, Functor g) =>
  Functor (PostCompose @c @c' @a g)
  where
  map_ = above

type Ran :: (x --> Types) -> (x --> z) -> NamesOf z -> Type
data Ran h g a where
  RAN ::
    Functor f =>
    Proxy f ->
    ((f ∘ g) ~> h) ->
    Act f a ->
    Ran h g a

-- NOTE: currently y is always Types
data (/) :: (x --> y) -> (x --> z) -> (z --> y)

type instance Act (h / g) o = Ran h g o

instance (Category x, Category z) => Functor ((/) @x @Types @z h g) where
  map_ zab (RAN (pf :: Proxy f) fgh fa) =
    RAN pf fgh (map @f zab fa)

-- NOTE: currently y is always Types
data PostRan :: (x --> z) -> (y ^ x) --> (y ^ z)

type instance Act (PostRan g) h = h / g

instance
  (Category x, Category z, Functor g) =>
  Functor (PostRan @x @z @Types g)
  where
  map_ ab =
    EXP \_ (RAN p fga fi) ->
      RAN p (ab ∘ fga) fi

instance (Functor g) => PostCompose g ⊣ PostRan @x @z @Types g where
  leftAdjoint_ a_bg =
    EXP \(Proxy :: Proxy i) ag ->
      case runExp @(Act g i) a_bg ag of
        RAN _ fg_b fgi ->
          runExp @i fg_b fgi

  rightAdjoint_ ag_b =
    EXP \(Proxy :: Proxy i) (a :: Act a i) ->
      RAN (Proxy @a) ag_b a

type Codensity :: (x --> Types) -> (Types --> Types)
type Codensity f = f / f

--

-- do notationy stuff

bindImpl ::
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
bindImpl _ m t =
  join @m @b
    (map @m t m :: Act (m ∘ m) b)

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
makeBind = BindDo (bindImpl @m)

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

egDuped :: (Prelude.Integer, Prelude.Integer)
egDuped = monadDo @Dup do
  v <- (10, 100)
  x <- (v Prelude.+ 1, v Prelude.+ 2)
  pure (x Prelude.* 2)

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

postinc :: State Prelude.Integer Prelude.Integer
postinc = stateMonad do
  x <- get
  _ <- put (x Prelude.+ 1)
  pure x

twicePostincShow :: State Prelude.Integer Prelude.String
twicePostincShow = stateMonad do
  a <- postinc
  b <- postinc
  c <- pure $ dupMonad do
    v <- (10, 100)
    x <- (v Prelude.+ 1, v Prelude.+ 2)
    pure (x Prelude.* 2 :: Prelude.Integer)
  pure $
    Foldable.fold
      [Prelude.show a, "-", Prelude.show b, "-", Prelude.show c]

egState :: (Prelude.String, Prelude.Integer)
egState = twicePostincShow 10

-- $> egState

newtype NT t m = NT (t ~> m)

type Free :: (Types --> Types) -> Type -> Type
data Free t a = FREE
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

data Free2 :: ((k ^ k) × k) --> k

type instance Act (Free0 f) o = Free f o

type instance Act Free1 f = Free0 f

type instance Act Free2 fx = Free (Fst fx) (Snd fx)

instance Functor (Free0 @Types t) where
  map_ (a_b :: a -> b) r = FREE do
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
  map_ ab = EXP \_ (FREE f) ->
    FREE \m a (NT tm) -> f m a (NT (tm ∘ ab))

instance Functor (Free2 @Types) where
  map_ (st :×: (ab :: Types a b)) = \(FREE f) ->
    FREE \(m :: Proxy m) _ (NT tm) ->
      map @m ab (f m (Proxy @a) (NT (tm ∘ st)))

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
  DAY_D :: Proxy x -> Proxy y -> k (Act p '(x, y)) z -> Act f x -> Act g y -> DayD @k p f g z

data
  DayF ::
    ((Types × Types) --> Types) ->
    (Types --> Types) ->
    (Types --> Types) ->
    (Types --> Types)

type instance Act (DayF p f g) x = DayD p f g x

instance Functor p => Functor (DayF p f g) where
  map_ (zw :: k z w) (DAY_D px py (xyz :: k xy z) fx gy) =
    DAY_D px py (zw ∘ xyz :: k xy w) fx gy

data
  Day ::
    ((Types × Types) --> Types) ->
    (((Types ^ Types) × (Types ^ Types)) --> (Types ^ Types))

type instance Act (Day p) '(f, g) = DayF p f g

instance Functor p => Functor (Day p) where
  map_ (EXP l :×: EXP r) =
    EXP \_p (DAY_D px py (xyz :: k xy z) fx gy) ->
      DAY_D
        px
        py
        xyz
        (l px fx)
        (r py gy)

data
  ProductD ::
    (Types --> Types) ->
    (Types --> Types) ->
    Type ->
    Type
  where
  PRODUCT_D ::
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
  map_ ab (PRODUCT_D fa ga) =
    PRODUCT_D
      (map @f ab fa)
      (map @g ab ga)

data Identity :: One --> (Types ^ Types)

type instance Act Identity t = Id

instance Functor Identity where
  map_ ONE = EXP \_ x -> x

instance Associative p => Associative (Day p) where
  lassoc_ = EXP \_p (DAY_D (px :: Proxy x) (_py :: Proxy y) xyz fx (DAY_D (pa :: Proxy a) (pb :: Proxy b) aby ga hb)) ->
    DAY_D
      Proxy
      pb
      ( xyz
          ∘ map @p
            ( identity @x :×: (aby :: Types (Act p '(a, b)) y)
            )
          ∘ rassoc @p @x @a @b
      )
      (DAY_D px pa (\x -> x) fx ga)
      hb
  rassoc_ = EXP \_p (DAY_D (_px :: Proxy x) (py :: Proxy y) xyz (DAY_D (pa :: Proxy a) (pb :: Proxy b) abx fa gb) hy) ->
    DAY_D
      pa
      Proxy
      ( xyz
          ∘ map @p
            ( (abx :: Types (Act p '(a, b)) x) :×: identity @y
            )
          ∘ lassoc @p @a @b @y
      )
      fa
      (DAY_D pb py (\x -> x) gb hy)

instance Monoidal (Day (∧)) Identity where
  idl = EXP \_p (DAY_D _ _ xyz x my :: DayD (∧) Id m z) -> map @m (\y -> xyz (x, y)) my
  coidl = EXP \_p my -> DAY_D Proxy Proxy (\(_, y) -> y) () my
  idr = EXP \_p (DAY_D _ _ xyz mx y :: DayD (∧) m Id z) -> map @m (\x -> xyz (x, y)) mx
  coidr = EXP \_p mx -> DAY_D Proxy Proxy (\(x, _) -> x) mx ()

instance
  Prelude.Applicative m =>
  MonoidObject
    (Day (∧))
    Identity
    (PreludeFunctor m)
  where
  mempty = EXP \_p x -> Prelude.pure x
  mappend = EXP \_p (DAY_D _ _ xyz fx fy) -> Prelude.liftA2 (\x y -> xyz (x, y)) fx fy

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

---

main :: Prelude.IO ()
main = Prelude.putStrLn ""
