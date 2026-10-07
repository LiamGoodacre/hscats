module ApplicativeChecks (checks) where

import Cats
import Cats.Applicative qualified as A
import Data.List.NonEmpty (NonEmpty (..))
import Prelude (Bool (..), Char, Int, String)
import Prelude qualified as P

-- Keep the constraints abstract: specializing these definitions to List alone
-- would let its concrete instances hide a missing superclass implication.
mapWithApply :: forall (f :: Types --> Types) a b. (A.Apply f) => (a -> b) -> Act f a -> Act f b
mapWithApply = map f

mapWithAlt :: forall (f :: Types --> Types) a b. (A.Alt f) => (a -> b) -> Act f a -> Act f b
mapWithAlt = map f

mapWithApplicative :: forall (f :: Types --> Types) a b. (A.Applicative f) => (a -> b) -> Act f a -> Act f b
mapWithApplicative = mapWithApply @f

applyWithApplicative :: forall (f :: Types --> Types). (A.Applicative f) => Day (∧) f f ~> f
applyWithApplicative = applyWithApply @f
  where
    applyWithApply :: forall g. (A.Apply g) => Day (∧) g g ~> g
    applyWithApply = A.lift2

applyWithAlternative :: forall (f :: Types --> Types). (A.Alternative f) => Day (∧) f f ~> f
applyWithAlternative = applyWithApplicative @f

altWithAlternative :: forall (f :: Types --> Types). (A.Alternative f) => Day (∨) f f ~> f
altWithAlternative = altWithAlt @f

altWithAlt :: forall (f :: Types --> Types). (A.Alt f) => Day (∨) f f ~> f
altWithAlt = A.lift2

-- This functor intentionally has choice without a product or a unit instance.
type data ChoiceOnly :: Types --> Types

type instance Act ChoiceOnly a = NonEmpty a

instance Functor ChoiceOnly where
  map _ = P.fmap

instance A.Lift2 (∨) ChoiceOnly where
  lift2 = EXP \_ (DataDayTypes k xs ys) ->
    P.fmap (k ∘ P.Left) xs P.<> P.fmap (k ∘ P.Right) ys

dayUnit :: forall (op :: BINARY_OP Types) -> (A.Lift0 op A.List) => MonoidalEmpty (Day₁ op) ~> A.List
dayUnit op = A.lift0 @_ @_ @op @A.List

multiply :: forall (op :: BINARY_OP Types) -> (A.Lift2 op A.List) => Day op A.List A.List ~> A.List
multiply _ = A.lift2

pureList :: forall a. a -> [a]
pureList = dayUnit (∧) $$ a

emptyList :: forall a. [a]
emptyList = (dayUnit (∨) $$ a) ()

productList :: forall a b c. (a -> b -> c) -> [a] -> [b] -> [c]
productList k xs ys = (multiply (∧) $$ c) (DataDayTypes (P.uncurry k) xs ys)

chooseList :: forall a b c. (a -> c) -> (b -> c) -> [a] -> [b] -> [c]
chooseList l r xs ys = (multiply (∨) $$ c) (DataDayTypes (P.either l r) xs ys)

-- These are the two sides of the documented associativity equation, using
-- the actual Day associator and bifunctor mapping from the library.
associateLeft ::
  forall (op :: BINARY_OP Types) ->
  (Functor op, A.Lift2 op A.List) =>
  Day op (Day op A.List A.List) A.List ~> A.List
associateLeft op = multiply op ∘ map (Day₁ op) (multiply op :×: identity A.List)

associateRight ::
  forall (op :: BINARY_OP Types) ->
  (Associative op, A.Lift2 op A.List) =>
  Day op (Day op A.List A.List) A.List ~> A.List
associateRight op =
  multiply op
    ∘ map (Day₁ op) (identity A.List :×: multiply op)
    ∘ rassoc (Day₁ op) A.List A.List A.List

unitLeft ::
  forall (op :: BINARY_OP Types) ->
  (Functor op, Monoidal (Day₁ @Types @Types op), A.LiftN op A.List) =>
  Day op (MonoidalEmpty (Day₁ op)) A.List ~> A.List
unitLeft op = multiply op ∘ map (Day₁ op) (dayUnit op :×: identity A.List)

unitRight ::
  forall (op :: BINARY_OP Types) ->
  (Functor op, Monoidal (Day₁ @Types @Types op), A.LiftN op A.List) =>
  Day op A.List (MonoidalEmpty (Day₁ op)) ~> A.List
unitRight op = multiply op ∘ map (Day₁ op) (identity A.List :×: dayUnit op)

ints :: [[Int]]
ints = [[], [0], [1, 2], [-3, 0, 4]]

bools :: [[Bool]]
bools = [[], [True], [False, True]]

chars :: [[Char]]
chars = [[], ['a'], ['b', 'c']]

checks :: [(String, Bool)]
checks =
  [ ("Applicative implies Apply and Functor", mapWithApplicative @A.List P.show [1 :: Int, 2] P.== ["1", "2"]),
    ( "Alternative implies Applicative",
      (applyWithAlternative @A.List $$ Int) (DataDayTypes (\(x, y) -> 10 P.* x P.+ y) [1, 2] [3, 4])
        P.== [13, 14, 23, 24]
    ),
    ( "Alternative implies Alt",
      (altWithAlternative @A.List $$ Int) (DataDayTypes (P.either (P.+ 1) (P.* 10)) [1, 2] [3, 4])
        P.== [2, 3, 30, 40]
    ),
    ( "Alt needs neither Apply nor a unit",
      (altWithAlt @ChoiceOnly $$ Int) (DataDayTypes (P.either (P.+ 1) (P.* 10)) (1 :| [2]) (3 :| [4]))
        P.== (2 :| [3, 30, 40])
    ),
    ("Alt implies Functor", mapWithAlt @ChoiceOnly P.show (1 :| [2 :: Int]) P.== ("1" :| ["2"])),
    ("Applicative List singleton injection", pureList (7 :: Int) P.== [7]),
    ("Alternative List empty choice", emptyList @Int P.== []),
    ("Apply List combination order", productList (\x y -> 10 P.* x P.+ y) [1, 2 :: Int] [3, 4] P.== [13, 14, 23, 24]),
    ("Alt List mapped concatenation", chooseList P.fromEnum P.fromEnum [True, False] ['a', 'b'] P.== [1, 0, 97, 98]),
    ("Apply List empty left operand", P.all (\xs -> productList ((P.+) @Int) [] xs P.== []) ints),
    ("Apply List empty right operand", P.all (\xs -> productList ((P.+) @Int) xs [] P.== []) ints),
    ("Alt List empty left operand", P.all (\xs -> chooseList P.id (P.+ 1) [] xs P.== P.map (P.+ 1) xs) ints),
    ("Alt List empty right operand", P.all (\xs -> chooseList (P.* 2) P.id xs [] P.== P.map (P.* 2) xs) ints),
    ( "Apply List naturality",
      P.and
        [ let day = DataDayTypes (\(x, b) -> if b then x else P.negate x) xs bs
           in P.map P.show ((multiply (∧) $$ Int) day)
                P.== (multiply (∧) $$ String) (map (Day (∧) A.List A.List) P.show day)
        | xs <- ints, bs <- bools
        ]
    ),
    ( "Alt List naturality",
      P.and
        [ let day = DataDayTypes (P.either (P.* 3) P.fromEnum) xs bs
           in P.map P.show ((multiply (∨) $$ Int) day)
                P.== (multiply (∨) $$ String) (map (Day (∨) A.List A.List) P.show day)
        | xs <- ints, bs <- bools
        ]
    ),
    ("Applicative List unit naturality", P.all (\x -> P.map P.even (pureList x) P.== pureList (P.even x)) [-3 .. 3 :: Int]),
    ("Alternative List unit naturality", P.map P.show (emptyList @Int) P.== emptyList @String),
    ( "Apply List respects maps of hidden objects",
      P.and
        [ productList (\x y -> x P.- y) (map A.List (P.+ 5) xs) (map A.List P.fromEnum bs)
            P.== productList (\x b -> (x P.+ 5) P.- P.fromEnum b) xs bs
        | xs <- ints, bs <- bools
        ]
    ),
    ( "Alt List respects maps of hidden objects",
      P.and
        [ chooseList (P.* 2) (P.+ 7) (map A.List (P.+ 5) xs) (map A.List P.fromEnum bs)
            P.== chooseList (\x -> 2 P.* (x P.+ 5)) (\b -> P.fromEnum b P.+ 7) xs bs
        | xs <- ints, bs <- bools
        ]
    ),
    ( "Apply List associativity",
      P.and
        [ let day = DataDayTypes (\(n, c) -> 10 P.* n P.+ P.fromEnum c)
                (DataDayTypes (\(x, b) -> if b then x else P.negate x) xs bs) cs
           in (associateLeft (∧) $$ Int) day P.== (associateRight (∧) $$ Int) day
        | xs <- ints, bs <- bools, cs <- chars
        ]
    ),
    ( "Alt List associativity",
      P.and
        [ let day = DataDayTypes (P.either (P.+ 10) P.fromEnum)
                (DataDayTypes (P.either (P.* 2) P.fromEnum) xs bs) cs
           in (associateLeft (∨) $$ Int) day P.== (associateRight (∨) $$ Int) day
        | xs <- ints, bs <- bools, cs <- chars
        ]
    ),
    ( "Applicative List left unit",
      P.all (\xs -> let day = DataDayTypes (\(n, x) -> n P.+ x) 7 xs
                    in (unitLeft (∧) $$ Int) day P.== (idl @_ @(Day₁ (∧)) @A.List $$ Int) day) ints
    ),
    ( "Applicative List right unit",
      P.all (\xs -> let day = DataDayTypes (\(x, b) -> if b then x else P.negate x) xs False
                    in (unitRight (∧) $$ Int) day P.== (idr @_ @(Day₁ (∧)) @A.List $$ Int) day) ints
    ),
    ( "Alternative List left unit",
      P.all (\xs -> let day = DataDayTypes (P.either (P.length @[]) (P.* 3)) () xs
                    in (unitLeft (∨) $$ Int) day P.== (idl @_ @(Day₁ (∨)) @A.List $$ Int) day) ints
    ),
    ( "Alternative List right unit",
      P.all (\xs -> let day = DataDayTypes (P.either (P.* 3) (P.length @[])) xs ()
                    in (unitRight (∨) $$ Int) day P.== (idr @_ @(Day₁ (∨)) @A.List $$ Int) day) ints
    ),
    ( "Applicative List map agrees with product and unit",
      P.all (\xs -> map A.List P.show xs P.== productList (\x () -> P.show x) xs (pureList ())) ints
    ),
    ( "Day monoid product unit adapter for Constructor",
      (A.lift0FromMonoidObject (∧) (type (Constructor [])) $$ Int) 7 P.== [7]
    ),
    ( "Day monoid coproduct unit adapter for Constructor",
      (A.lift0FromMonoidObject (∨) (type (Constructor [])) $$ Int) () P.== []
    ),
    ( "Day monoid product adapter for Constructor",
      (A.lift2FromMonoidObject (∧) (type (Constructor [])) $$ Int)
        (DataDayTypes (\(x, y) -> 10 P.* x P.+ y) [1, 2] [3, 4]) P.== [13, 14, 23, 24]
    ),
    ( "Day monoid coproduct adapter for Constructor",
      (A.lift2FromMonoidObject (∨) (type (Constructor [])) $$ Int)
        (DataDayTypes (P.either (P.+ 1) P.fromEnum) [1, 2] [True, False]) P.== [2, 3, 1, 0]
    )
  ]
