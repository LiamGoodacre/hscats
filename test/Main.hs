module Main where

import Cats
import Data.Foldable qualified as Foldable
import Data.Kind
import Data.Proxy
import Data.Type.Equality (type (~))
import DayChecks qualified
import DayInstances (Dup, Duping)
import DayUnsupported qualified
import Do (pure)
import Do qualified
import OppositeChecks qualified
import ProcomposeChecks qualified
import RecursionSchemes
import SpanChecks qualified
import Uncategorised
import Prelude (($))
import Prelude qualified

{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: {getPreludeMonoid :: m} -> PreludeMonoid m '() '()

type instance Obj (PreludeMonoid m) x = (x ~ '())

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

type instance Obj (Endo o c) x = (x ~ '())

instance (Semigroupoid c, o ∈ c) => Semigroupoid (Endo o c) where
  ENDO l ∘ ENDO r = ENDO (l ∘ r)

instance (Category c, o ∈ c) => Category (Endo o c) where
  identity _ = ENDO (identity _)

{- Functor: examples -}

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
    EXP \(type i) ag ->
      case (a_bg $$ Act g i) ag of
        RAN _ fg_b fgi ->
          (fg_b $$ i) fgi

  leftToRight _ _ ag_b =
    EXP \_ -> RAN Proxy ag_b

type Codensity :: (x --> Types) -> (Types --> Types)
type Codensity f = f / f

---

dupMonad :: Do.AdjunctionMonadDo Duping
dupMonad = Do.with _

egDuped :: (Prelude.Integer, Prelude.Integer)
egDuped = Do.with Duping Do.do
  v <- (10, 100)
  x <- (v Prelude.+ 1, v Prelude.+ 2)
  pure (x Prelude.* 2)

-- !$> egDuped -- (22,204)

type Stating s = '(Reader s, Env s)

type States s = Reader s • Env s

stateMonad :: Do.AdjunctionMonadDo (Stating s)
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

-- !$> egState -- ("10-11-(22,204)",12)

newtype NT t m = NT (t ~> m)

type Free :: (Types --> Types) -> Type -> Type
data Free t a = FREE
  { runFree ::
      forall m a' ->
      (AdjunctionMonadBy m Types, a' ~ a) =>
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
  map _ a_b = EXP \_ (FREE f) -> FREE \m (type a) (NT t_m) -> f m a (NT (t_m ∘ a_b))

instance Functor (Free2 @Types) where
  map _ (s_t :×: (a_b :: Types a b)) = \(FREE f) ->
    FREE \m _ (NT t_m) ->
      map m a_b (f m a (NT (t_m ∘ s_t)))

---

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

lift0 :: forall a. forall (m :: Types --> Types) -> (MonoidObject (Day₁ (∧)) m) => a -> Act m a
lift0 m = member (type Types) (type a) do
  empty (type (Day₁ (∧))) (type m) $$ a

lift2 ::
  forall c a b.
  forall (m :: Types --> Types) ->
  (MonoidObject (Day₁ (∧)) m) =>
  (a -> b -> c) ->
  Act m a ->
  Act m b ->
  Act m c
lift2 m abc ma mb =
  -- Supply every object dictionary required by DataDayTypes explicitly to
  -- avoid recursive quantified-constraint resolution in the multi-unit REPL.
  member (type Types) (type a) do
    member (type Types) (type b) do
      member (type Types) (type c) do
        (append (type (Day₁ (∧))) (type m) $$ c)
          (DataDayTypes @a @b @c (\(a, b) -> abc a b) ma mb)

_egLift0Id :: Prelude.Int -> Prelude.Int
_egLift0Id = lift0 Id

_egLift0Dup :: Prelude.Int -> (Prelude.Int, Prelude.Int)
_egLift0Dup = lift0 Dup

_egLift0List :: Prelude.Int -> [Prelude.Int]
_egLift0List = lift0 List

-- instance
--   (Prelude.Monad m) =>
--   MonoidObject Composing Id (Constructor m)
--   where
--   empty = EXP \_ -> Prelude.pure
--   append _ _ = EXP \_ -> (Prelude.>>= identity _)
--
-- join0 :: forall m. (MonoidObject Composing Id m) => Id ~> m
-- join0 = empty @Composing
--
-- join2 :: forall m. (MonoidObject Composing Id m) => (m • m) ~> m
-- join2 = append @Composing

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
  (k --> k) ->
  Constraint
class
  (Monoidal p) =>
  Foldable p (t :: k --> k)
  where
  foldMap_ ::
    (a ∈ k, m ∈ k, MonoidObject p m) =>
    k a m ->
    k (Act t a) m

foldMap ::
  forall {k} (t :: k --> k) p m a.
  (Foldable p t, a ∈ k, m ∈ k, MonoidObject p m) =>
  k a m ->
  k (Act t a) m
foldMap = foldMap_ @k @p @t @a @m

instance Foldable (∧) List where
  foldMap_ _ [] = empty (type (∧)) (type _) ()
  foldMap_ f (h : t) = f h <> foldMap @List @(∧) f t

-- Types () m
-- Types (m, m) m
-- (Types ^ Types) Id m
-- (Types ^ Types) (Day (∧) m m) m

-- t m -> m
-- t • m -> m • t

type Traversable ::
  BINARY_OP (k ^ k) ->
  (k --> k) ->
  Constraint
class (Monoidal p) => Traversable p t where
  sequence ::
    forall p' t' m ->
    (p' ~ p, t' ~ t, MonoidObject p m) =>
    (t • m) ~> (m • t)

sequenceA ::
  forall i.
  forall t m ->
  (Traversable (Day₁ (∧)) t, MonoidObject (Day₁ (∧)) m) =>
  Act (t • m) i -> Act (m • t) i
sequenceA t m = member (type Types) (type i) do
  sequence (Day₁ (∧)) t m $$ i

instance Traversable (Day₁ (∧)) Id where
  sequence ::
    forall p' t' m ->
    (p' ~ Day₁ (∧), t' ~ Id, MonoidObject (Day₁ (∧)) m) =>
    (Id • m) ~> (m • Id)
  sequence _ _ m = EXP \(type i) -> identity m $$ i

instance Traversable (Day₁ (∧)) List where
  sequence ::
    forall p' t' m ->
    (p' ~ Day₁ (∧), t' ~ List, MonoidObject (Day₁ (∧)) m) =>
    (List • m) ~> (m • List)
  sequence _ _ m = EXP \i ->
    Prelude.foldr
      (lift2 m ((:) @i))
      (lift0 m ([] @i))

instance Traversable (Day₁ (∧)) Dup where
  sequence ::
    forall p' t' m ->
    (p' ~ Day₁ (∧), t' ~ Dup, MonoidObject (Day₁ (∧)) m) =>
    (Dup • m) ~> (m • Dup)
  sequence _ _ m = EXP \i (l, r) -> lift2 @(Act Dup i) m (,) l r

_egSeqId :: Prelude.Int -> Prelude.String
_egSeqId =
  (Id `sequenceA` Constructor _)
    Prelude.show

_egSeqList :: Prelude.Int -> [Prelude.String]
_egSeqList =
  (List `sequenceA` Constructor _)
    [Prelude.show, Prelude.show]

_egSeqDup :: Prelude.Int -> (Prelude.String, Prelude.String)
_egSeqDup =
  (Dup `sequenceA` Constructor _)
    (Prelude.show, Prelude.show)

---

class TraversableV2 p t where
  traverse_ ::
    (MonoidObject p m) =>
    (Δ' a ~> m) ->
    ((t • Δ' a) ~> (m • t))

instance TraversableV2 (Day₁ (∧)) List where
  traverse_ ::
    forall m a.
    (MonoidObject (Day₁ (∧)) m) =>
    (Δ' a ~> m) ->
    ((List • Δ' a) ~> (m • List))
  traverse_ (EXP f) =
    EXP \i ->
      Prelude.foldr
        (lift2 @[i] m (:) ∘ f i)
        (lift0 m ([] @i))

---

assertEqual ::
  (Prelude.Eq a, Prelude.Show a) =>
  Prelude.String -> a -> a -> Prelude.IO ()
assertEqual label expected actual
  | expected Prelude.== actual = Prelude.pure ()
  | Prelude.otherwise =
      Prelude.ioError $
        Prelude.userError $
          label
            Prelude.++ ": expected "
            Prelude.++ Prelude.show expected
            Prelude.++ ", got "
            Prelude.++ Prelude.show actual

checks :: [Prelude.IO ()]
checks =
  [ assertEqual "Dup do" (22, 204) egDuped,
    assertEqual "State do" ("10-11-(22,204)", 12) egState,
    assertEqual "State postincrement" (5, 6) (postinc 5),
    assertEqual "lift0 Id" 7 (_egLift0Id 7),
    assertEqual "lift0 Dup" (7, 7) (_egLift0Dup 7),
    assertEqual "lift0 List" [7] (_egLift0List 7),
    assertEqual @[Prelude.Int]
      "lift2 List"
      [11, 21, 12, 22]
      (lift2 List (Prelude.+) [1, 2] [10, 20]),
    assertEqual @(Prelude.Int, Prelude.Int)
      "lift2 Dup"
      (11, 22)
      (lift2 Dup (Prelude.+) (1, 2) (10, 20)),
    assertEqual "sequence Id" "7" (_egSeqId 7),
    assertEqual "sequence List" ["7", "7"] (_egSeqList 7),
    assertEqual "sequence Dup" ("7", "7") (_egSeqDup 7),
    assertEqual @[[Prelude.Int]]
      "sequence empty List"
      [[]]
      (sequenceA List List []),
    assertEqual @[[Prelude.Int]]
      "sequence List combinations"
      [[1, 10], [1, 20], [2, 10], [2, 20]]
      (sequenceA List List [[1, 2], [10, 20]]),
    assertEqual
      "foldMap empty List"
      ""
      (foldMap @List @(∧) Prelude.show ([] :: [Prelude.Int])),
    assertEqual "foldMap List" "123" (foldMap @List @(∧) Prelude.show _abc),
    assertEqual "list refix" [1, 2, 3] _abc,
    assertEqual
      "Fix round trip"
      _abc
      (refix @(FixOf (AsFunctor (ListF Prelude.Int))) @(AnObject Types [Prelude.Int]) _def),
    assertEqual
      "cata List"
      6
      ( cata @(AnObject Types [Prelude.Int]) @Prelude.Int
          (\case Nil -> 0; Cons x total -> x Prelude.+ total)
          _abc
      ),
    assertEqual
      "ana List"
      [3, 2, 1]
      ( ana @(AnObject Types [Prelude.Int]) @Prelude.Int
          (\case 0 -> Nil; n -> Cons n (n Prelude.- 1))
          3
      )
  ]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- SpanChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- DayChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- OppositeChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ProcomposeChecks.checks]
    Prelude.++ [DayUnsupported.check]

main :: Prelude.IO ()
main =
  Prelude.sequence_ checks
    Prelude.>> Prelude.putStrLn (Prelude.show (Prelude.length checks) Prelude.++ " example checks passed.")
