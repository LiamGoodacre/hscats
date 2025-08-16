module Main where

import Cats
import Data.Foldable qualified as Foldable
import Data.Kind
import Data.Proxy
import Data.Type.Equality (type (~))
import Do (pure)
import Do qualified
import RecursionSchemes
import Prelude (($))
import Prelude qualified

{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: {getPreludeMonoid :: m} -> PreludeMonoid m '() '()

type instance x ∈ PreludeMonoid m = (x ~ '())

instance (Prelude.Semigroup m) => Semigroupoid (PreludeMonoid m) where
  PreludeMonoid l ∘ PreludeMonoid r = PreludeMonoid (l Prelude.<> r)

instance (Prelude.Monoid m) => Category (PreludeMonoid m) where
  identity _ = PreludeMonoid Prelude.mempty

boring_monoid_category_example :: ()
boring_monoid_category_example = ()
  where
    _monoid_mappend :: (Monoid c o) => c o o -> c o o -> c o o
    _monoid_mappend = (∘)

    _monoid_mempty :: (Monoid c o) => c o o
    _monoid_mempty = identity _

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
  identity _ = ENDO (identity _)

{- Functor: examples -}

-- Prelude.Functor is a specialisation of Functor
type data PreludeFunctor (f :: Type -> Type) :: Types --> Types

type instance Act (PreludeFunctor f) a = f a

instance (Prelude.Functor f) => Functor (PreludeFunctor f) where
  map _ = Prelude.fmap

-- Parallel functor product

type data (***) :: (a --> s) -> (b --> t) -> ((a × b) --> (s × t))

type instance Act (f *** g) o = '(Act f (Fst o), Act g (Snd o))

instance (Functor f, Functor g) => Functor (f *** g) where
  map _ (l :×: r) = map f l :×: map g r

-- Pointwise functor product

type data (&&&) :: (d --> l) -> (d --> r) -> (d --> (l × r))

type instance Act (f &&& g) o = '(Act f o, Act g o)

instance (Functor f, Functor g) => Functor (f &&& g) where
  map _ t = map f t :×: map g t

{- Adjunctions: examples -}

-- Env s ⊣ Reader s

type data Reader :: Type -> (Types --> Types)

type instance Act (Reader x) y = x -> y

instance Functor (Reader x) where
  map _ = (∘)

type data Env :: Type -> (Types --> Types)

type instance Act (Env x) y = (y, x)

instance Functor (Env x) where
  map _ f (l, r) = (f l, r)

instance Env s ⊣ Reader s where
  rightToLeft _ _ = Prelude.uncurry
  leftToRight _ _ = Prelude.curry

-- (• g) ⊣ (/ g)
-- aka (PostCompose g ⊣ PostRan g)

type data PostCompose :: (c --> c') -> (a ^ c') --> (a ^ c)

type instance Act (PostCompose g) f = f • g

instance
  (Category c, Category c', Category a, Functor g) =>
  Functor (PostCompose @c @c' @a g)
  where
  map _ = above

type Ran :: (x --> Types) -> (x --> z) -> NamesOf z -> Type
data Ran h g a where
  RAN ::
    (Functor f) =>
    Proxy f ->
    ((f • g) ~> h) ->
    Act f a ->
    Ran h g a

-- NOTE: currently y is always Types
type data (/) :: (x --> y) -> (x --> z) -> (z --> y)

type instance Act (h / g) o = Ran h g o

instance (Category x, Category z) => Functor ((/) @x @Types @z h g) where
  map _ zab (RAN (Proxy @f) fgh fa) =
    RAN (Proxy @f) fgh (map f zab fa)

-- NOTE: currently y is always Types
type data PostRan :: (x --> z) -> (y ^ x) --> (y ^ z)

type instance Act (PostRan g) h = h / g

instance
  (Category x, Category z, Functor g) =>
  Functor (PostRan @x @z @Types g)
  where
  map _ ab =
    EXP \_ (RAN p fga fi) ->
      RAN p (ab ∘ fga) fi

instance (Functor g) => PostCompose g ⊣ PostRan @x @z @Types g where
  rightToLeft _ _ a_bg =
    EXP \i ag ->
      case (a_bg $$ Act g i) ag of
        RAN _ fg_b fgi ->
          (fg_b $$ i) fgi

  leftToRight _ _ ag_b =
    EXP \_ -> RAN Proxy ag_b

type Codensity :: (x --> Types) -> (Types --> Types)
type Codensity f = f / f

---

type Dup = (∧) • Δ₂ Types

dupMonad :: Do.MonadDo Dup
dupMonad = Do.with _

egDuped :: (Prelude.Integer, Prelude.Integer)
egDuped = Do.with Dup Do.do
  v <- (10, 100)
  x <- (v Prelude.+ 1, v Prelude.+ 2)
  pure (x Prelude.* 2)

-- !$> egDuped -- (22,204)

type States s = Reader s • Env s

stateMonad :: Do.MonadDo (States s)
stateMonad = Do.with _

type State s i = Act (States s) i

get :: State s s
get s = (s, s)

put :: s -> State s ()
put v _ = ((), v)

modify :: (s -> s) -> State s ()
modify t s = ((), t s)

postinc :: State Prelude.Integer Prelude.Integer
postinc = stateMonad Do.do
  x <- get
  _ <- put (x Prelude.+ 1)
  pure x

twicePostincShow :: State Prelude.Integer Prelude.String
twicePostincShow = stateMonad Do.do
  a <- postinc
  b <- postinc
  let c = dupMonad Do.do
        v <- (10, 100)
        x <- (v Prelude.+ 1, v Prelude.+ 2)
        pure (x Prelude.* 2 :: Prelude.Integer)
  pure $
    Foldable.fold
      [Prelude.show a, "-", Prelude.show b, "-", Prelude.show c]

egState :: (Prelude.String, Prelude.Integer)
egState = twicePostincShow 10

-- !$> egState

newtype NT t m = NT (t ~> m)

type Free :: (Types --> Types) -> Type -> Type
data Free t a = FREE
  { runFree ::
      forall m a' ->
      (MonadBy m Types, a' ~ a) =>
      NT t m ->
      Act m a
  }

type data Free0 :: (k --> k) -> (k --> k)

type data Free1 :: (k ^ k) --> (k ^ k)

type data Free2 :: ((k ^ k) × k) --> k

type instance Act (Free0 f) o = Free f o

type instance Act Free1 f = Free0 f

type instance Act Free2 fx = Free (Fst fx) (Snd fx)

instance Functor (Free0 @Types t) where
  map _ (a_b :: a -> b) r = FREE \m _ t_m -> map m a_b (runFree r m a t_m)

instance Functor (Free1 @Types) where
  map _ a_b = EXP \_ (FREE f) -> FREE \m a (NT t_m) -> f m a (NT (t_m ∘ a_b))

instance Functor (Free2 @Types) where
  map _ (s_t :×: (a_b :: Types a b)) = \(FREE f) ->
    FREE \m _ (NT t_m) ->
      map m a_b (f m a (NT (t_m ∘ s_t)))

---

type OldDayD ::
  forall {i}.
  forall (k :: CATEGORY i).
  ((k × k) --> k) ->
  (k --> Types) ->
  (k --> Types) ->
  i ->
  Type
data OldDayD p f g z where
  DAY_D :: Proxy x -> Proxy y -> k (Act p '(x, y)) z -> Act f x -> Act g y -> OldDayD @k p f g z

day ::
  forall
    {i}
    {k :: CATEGORY i}
    (p :: (k × k) --> k)
    (x :: i)
    (y :: i)
    (z :: i)
    (f :: k --> Types)
    (g :: k --> Types).
  k (Act p '(x, y)) z ->
  Act f x ->
  Act g y ->
  OldDayD p f g z
day = DAY_D @x @y @k @p @z @f @g Proxy Proxy

type data
  OldDayF ::
    ((Types × Types) --> Types) ->
    (Types --> Types) ->
    (Types --> Types) ->
    (Types --> Types)

type instance Act (OldDayF p f g) x = OldDayD p f g x

instance (Functor p) => Functor (OldDayF p f g) where
  map _ (zw :: k z w) (DAY_D px py (xyz :: k xy z) fx gy) =
    DAY_D px py (zw ∘ xyz :: k xy w) fx gy

type data
  OldDay ::
    ((Types × Types) --> Types) ->
    (((Types ^ Types) × (Types ^ Types)) --> (Types ^ Types))

type instance Act (OldDay p) '(f, g) = OldDayF p f g

instance (Functor p) => Functor (OldDay p) where
  map _ (EXP l :×: EXP r) =
    EXP \_p (DAY_D (Proxy @px) (Proxy @py) (xyz :: k xy z) fx gy) ->
      DAY_D
        (Proxy @px)
        (Proxy @py)
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

type data ProductF :: (Types --> Types) -> (Types --> Types) -> (Types --> Types)

type instance Act (ProductF f g) x = ProductD f g x

instance
  ( Functor f,
    Functor g
  ) =>
  Functor (ProductF f g)
  where
  map _ ab (PRODUCT_D fa ga) =
    PRODUCT_D
      (map f ab fa)
      (map g ab ga)

instance (Associative p) => Associative (OldDay p) where
  lassoc _ _ _ _ = EXP \_ (DAY_D (Proxy @x) Proxy xyz fx (DAY_D (Proxy @a) (Proxy @b) aby ga hb)) ->
    DAY_D
      Proxy
      (Proxy @b)
      (xyz ∘ map p (identity x :×: aby) ∘ rassoc p x a b)
      (DAY_D (Proxy @x) (Proxy @a) (identity _) fx ga)
      hb
  rassoc _ _ _ _ = EXP \_ (DAY_D Proxy (Proxy @y) xyz (DAY_D (Proxy @a) (Proxy @b) abx fa gb) hy) ->
    DAY_D
      (Proxy @a)
      Proxy
      (xyz ∘ map p (abx :×: identity y) ∘ lassoc p a b y)
      fa
      (DAY_D (Proxy @b) (Proxy @y) (identity _) gb hy)

instance Monoidal (OldDay (∧)) Id where
  idl = EXP \_ (DAY_D _ _ xyz x my :: OldDayD (∧) Id m z) -> map m (\y -> xyz (x, y)) my
  coidl = EXP \_ my -> DAY_D Proxy Proxy Prelude.snd () my
  idr = EXP \_ (DAY_D _ _ xyz mx y :: OldDayD (∧) m Id z) -> map m (\x -> xyz (x, y)) mx
  coidr = EXP \_ mx -> DAY_D Proxy Proxy Prelude.fst mx ()

instance
  (Prelude.Applicative m) =>
  MonoidObject (OldDay (∧)) Id (PreludeFunctor m)
  where
  empty_ = EXP \_p x -> Prelude.pure x
  append_ = EXP \_p (DAY_D _ _ xyz fx fy) ->
    Prelude.liftA2 (\x y -> xyz (x, y)) fx fy

instance MonoidObject (OldDay (∧)) Id Id where
  empty_ = EXP \_p x -> x
  append_ = EXP \_p (DAY_D _ _ xyz fx fy) -> xyz (fx, fy)

instance MonoidObject (OldDay (∧)) Id Dup where
  empty_ = EXP \_p x -> (x, x)
  append_ = EXP \_p (DAY_D _ _ xyz (fx0, fx1) (fy0, fy1)) ->
    (xyz (fx0, fy0), xyz (fx1, fy1))

instance MonoidObject (OldDay (∧)) Id List where
  empty_ = EXP \_p x -> [x]
  append_ = EXP \_p (DAY_D _ _ xyz fx fy) ->
    Prelude.liftA2 (\x y -> xyz (x, y)) fx fy

lift0 :: forall a. forall m -> (MonoidObject (OldDay (∧)) Id m) => a -> Act m a
lift0 m = empty @(OldDay (∧)) @m $$ a

lift2 ::
  forall c a b.
  forall m ->
  (MonoidObject (OldDay (∧)) Id m) =>
  (a -> b -> c) ->
  Act m a ->
  Act m b ->
  Act m c
lift2 m abc ma mb =
  (append @(OldDay (∧)) @m $$ c)
    (day @_ @a @b @c (\(a, b) -> abc a b) ma mb)

_egLift0Id :: Prelude.Int -> Prelude.Int
_egLift0Id = lift0 Id

_egLift0Dup :: Prelude.Int -> (Prelude.Int, Prelude.Int)
_egLift0Dup = lift0 Dup

_egLift0List :: Prelude.Int -> [Prelude.Int]
_egLift0List = lift0 List

instance
  (Prelude.Monad m) =>
  MonoidObject Composing Id (PreludeFunctor m)
  where
  empty_ = EXP \_ -> Prelude.pure
  append_ = EXP \_ -> (Prelude.>>= identity _)

join0 :: forall m. (MonoidObject Composing Id m) => Id ~> m
join0 = empty @Composing

join2 :: forall m. (MonoidObject Composing Id m) => (m • m) ~> m
join2 = append @Composing

---

type data ArrTo :: forall (k :: CATEGORY i) -> i -> Op k --> Types

type instance Act (ArrTo k r) a = k a r

instance (Category k, r ∈ k) => Functor (ArrTo k r) where
  map _ (OP ba) = (∘ ba)

type data OpArrTo :: forall (k :: CATEGORY i) -> i -> k --> Op Types

type instance Act (OpArrTo k r) a = k a r

instance (Category k, r ∈ k) => Functor (OpArrTo k r) where
  map _ ba = OP (∘ ba)

instance OpArrTo Types r ⊣ ArrTo Types r where
  rightToLeft _ _ = OP ∘ Prelude.flip
  leftToRight _ _ = Prelude.flip ∘ runOP

-- Foldable?

type Foldable ::
  forall {i}.
  forall (k :: CATEGORY i).
  BINARY_OP k ->
  i ->
  (k --> k) ->
  Constraint
class
  (Monoidal p id) =>
  Foldable p id (t :: k --> k)
    | p -> id
  where
  foldMap_ ::
    (a ∈ k, m ∈ k, MonoidObject p id m) =>
    k a m ->
    k (Act t a) m

foldMap ::
  forall {k} (t :: k --> k) p {id} m a.
  (Foldable p id t, a ∈ k, m ∈ k, MonoidObject p id m) =>
  k a m ->
  k (Act t a) m
foldMap = foldMap_ @k @p @id @t @a @m

instance Foldable (∧) () List where
  foldMap_ _ [] = empty @(∧) ()
  foldMap_ f (h : t) = f h <> foldMap @List @(∧) f t

-- Types () m
-- Types (m, m) m
-- (Types ^ Types) Id m
-- (Types ^ Types) (OldDay (∧) m m) m

-- t m -> m
-- t • m -> m • t

type Traversable ::
  BINARY_OP (k ^ k) ->
  (k --> k) ->
  (k --> k) ->
  Constraint
class (Monoidal p id) => Traversable p id t | p -> id where
  sequence ::
    forall p' t' m ->
    (p' ~ p, t' ~ t, MonoidObject p id m) =>
    (t • m) ~> (m • t)

sequenceA ::
  forall i.
  forall t m ->
  (Traversable (OldDay (∧)) Id t, MonoidObject (OldDay (∧)) Id m) =>
  Act (t • m) i -> Act (m • t) i
sequenceA t m = sequence (OldDay (∧)) t m $$ i

instance Traversable (OldDay (∧)) Id Id where
  sequence ::
    forall p' t' m ->
    (p' ~ OldDay (∧), t' ~ Id, MonoidObject (OldDay (∧)) Id m) =>
    (Id • m) ~> (m • Id)
  sequence _ _ m = EXP \i -> identity (Act m i)

instance Traversable (OldDay (∧)) Id List where
  sequence ::
    forall p' t' m ->
    (p' ~ OldDay (∧), t' ~ List, MonoidObject (OldDay (∧)) Id m) =>
    (List • m) ~> (m • List)
  sequence _ _ m = EXP \i ->
    Prelude.foldr
      (lift2 m ((:) @i))
      (lift0 m ([] @i))

instance Traversable (OldDay (∧)) Id Dup where
  sequence ::
    forall p' t' m ->
    (p' ~ OldDay (∧), t' ~ Dup, MonoidObject (OldDay (∧)) Id m) =>
    (Dup • m) ~> (m • Dup)
  sequence _ _ m = EXP \i (l, r) -> lift2 @(Act Dup i) m (,) l r

_egSeqId :: Prelude.Int -> Prelude.String
_egSeqId =
  (Id `sequenceA` PreludeFunctor _)
    Prelude.show

_egSeqList :: Prelude.Int -> [Prelude.String]
_egSeqList =
  (List `sequenceA` PreludeFunctor _)
    [Prelude.show, Prelude.show]

_egSeqDup :: Prelude.Int -> (Prelude.String, Prelude.String)
_egSeqDup =
  (Dup `sequenceA` PreludeFunctor _)
    (Prelude.show, Prelude.show)

---

class TraversableV2 p id t where
  traverse_ ::
    (MonoidObject p id m) =>
    (Δ' a ~> m) ->
    ((t • Δ' a) ~> (m • t))

instance TraversableV2 (OldDay (∧)) Id List where
  traverse_ ::
    forall m a.
    (MonoidObject (OldDay (∧)) Id m) =>
    (Δ' a ~> m) ->
    ((List • Δ' a) ~> (m • List))
  traverse_ (EXP f) =
    EXP \i ->
      Prelude.foldr
        (lift2 @[i] m (:) ∘ f i)
        (lift0 m ([] @i))

---

main :: Prelude.IO ()
main = Prelude.putStrLn ""
