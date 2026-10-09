module Main where

import AdjunctionChecks qualified
import ApplicativeChecks qualified
import ApplicativeHelpersChecks qualified
import Cats
import Cats.Do (pure)
import Cats.Do qualified as Do
import CoreLawChecks qualified
import CurryChecks qualified
import Data.Foldable qualified as Foldable
import Data.Kind
import Data.Type.Equality (type (~))
import DayChecks qualified
import DayConversionChecks qualified
import DayInstances (Dup)
import DayUnsupported qualified
import MonadChecks qualified
import MonoidalChecks qualified
import OppositeChecks qualified
import OpticChecks qualified
import ProcomposeChecks qualified
import ProcomposeStructureChecks qualified
import ProcomposeUnsupported qualified
import ProductChecks qualified
import RecursionObjects
import RecursionSchemes
import SpanChecks qualified
import Prelude (($))
import Prelude qualified

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

---

dupMonad :: Do.MonadDo (ViaAdjunction Dup)
dupMonad = Do.with (ViaAdjunction Dup)

egDuped :: (Prelude.Integer, Prelude.Integer)
egDuped = dupMonad Do.do
  v <- (10, 100)
  x <- (v Prelude.+ 1, v Prelude.+ 2)
  pure (x Prelude.* 2)

-- !$> egDuped -- (22,204)

type States s = Reader s • Env s

stateMonad :: forall s. Do.MonadDo (ViaAdjunction (States s))
stateMonad = Do.with (ViaAdjunction (States s))

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

---

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

---

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
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- AdjunctionChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ApplicativeChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ApplicativeHelpersChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- CoreLawChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- CurryChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ProductChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- SpanChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- DayChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- DayConversionChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- MonoidalChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- MonadChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- OpticChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- OppositeChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ProcomposeChecks.checks]
    Prelude.++ [assertEqual label Prelude.True result | (label, result) <- ProcomposeStructureChecks.checks]
    Prelude.++ [DayUnsupported.check, ProcomposeUnsupported.check]

main :: Prelude.IO ()
main =
  Prelude.sequence_ checks
    Prelude.>> Prelude.putStrLn (Prelude.show (Prelude.length checks) Prelude.++ " example checks passed.")
