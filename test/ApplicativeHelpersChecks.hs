module ApplicativeHelpersChecks (checks) where

import ApplicativeChecks (ChoiceOnly)
import Cats
import Cats.Applicative qualified as A
import Control.Applicative qualified as P
import Data.List.NonEmpty (NonEmpty (..))
import Prelude (Bool (..), Int, Maybe (..), String)
import Prelude qualified as P

type Lists = TypeConstructor []

type Optional = TypeConstructor Maybe

type Writer = TypeConstructor ((,) [String])

type Zipped = TypeConstructor P.ZipList

-- A product operation without a unit. The helper must not demand Applicative.
type data ApplyOnly :: Types --> Types

type instance Act ApplyOnly a = NonEmpty a

instance Functor ApplyOnly where
  map _ = P.fmap

instance A.Lift2 (∧) ApplyOnly where
  lift2 = EXP \_ (DataDayTypes k xs ys) -> P.liftA2 (P.curry k) xs ys

-- Neither Functor nor Lift2 is available: the unit helpers need only Lift0.
type data UnitOnly :: Types --> Types

type instance Act UnitOnly a = Maybe a

instance A.Lift0 (∧) UnitOnly where
  lift0 _ _ = EXP \_ -> Just

instance A.Lift0 (∨) UnitOnly where
  lift0 _ _ = EXP \_ () -> Nothing

-- Keep these constraints abstract to check the advertised helper requirements.
combine :: forall (f :: Types --> Types) a b c. (A.Apply f) => (a -> b -> c) -> Act f a -> Act f b -> Act f c
combine = A.liftA2 f

choose :: forall (f :: Types --> Types) a b c. (A.Alt f) => (a -> c) -> (b -> c) -> Act f a -> Act f b -> Act f c
choose = A.chooseWith f

applyAbstract :: forall (f :: Types --> Types) a b. (A.Apply f) => Act f (a -> b) -> Act f a -> Act f b
applyAbstract = A.apply @a @b f

keepLeftAbstract :: forall (f :: Types --> Types) a b. (A.Apply f) => Act f a -> Act f b -> Act f a
keepLeftAbstract = A.keepLeft @a @b f

keepRightAbstract :: forall (f :: Types --> Types) a b. (A.Apply f) => Act f a -> Act f b -> Act f b
keepRightAbstract = A.keepRight @a @b f

chooseAbstract :: forall (f :: Types --> Types) a. (A.Alt f) => Act f a -> Act f a -> Act f a
chooseAbstract = A.choose @a f

ints :: [Maybe Int]
ints = [Nothing, Just (-2), Just 7]

bools :: [Maybe Bool]
bools = [Nothing, Just False, Just True]

render :: Int -> Bool -> String
render n b = if b then P.show n else "no"

checks :: [(String, Bool)]
checks =
  [ ("Constructor list pure", A.pure Lists (7 :: Int) P.== [7]),
    ("Constructor list blank", A.blank @Int Lists P.== []),
    ( "Constructor list product order",
      A.liftA2 Lists ((P.+) @Int) [1, 2] [10, 20] P.== [11, 21, 12, 22]
    ),
    ( "Constructor list mapped choice changes input types",
      A.chooseWith Lists P.show (\b -> if b then "yes" else "no") [1, 2 :: Int] [True, False]
        P.== ["1", "2", "yes", "no"]
    ),
    ( "Constructor list product handles either empty operand",
      A.liftA2 Lists ((P.+) @Int) [] [1, 2] P.== []
        P.&& A.liftA2 Lists ((P.+) @Int) [1, 2] [] P.== []
    ),
    ( "Constructor list choice handles either empty operand",
      A.chooseWith Lists P.show P.show ([] :: [Int]) [1, 2 :: Int] P.== ["1", "2"]
        P.&& A.chooseWith Lists P.show P.show [1, 2 :: Int] ([] :: [Int]) P.== ["1", "2"]
    ),
    ("Constructor Maybe pure", A.pure Optional (7 :: Int) P.== Just 7),
    ("Constructor Maybe blank", A.blank @Int Optional P.== Nothing),
    ( "Constructor Maybe product agrees with Prelude on present and missing operands",
      P.and [A.liftA2 Optional render n b P.== P.liftA2 render n b | n <- ints, b <- bools]
    ),
    ( "Constructor Maybe choice agrees with Control.Applicative",
      P.and [A.chooseWith Optional P.show P.show n b P.== (P.fmap P.show n P.<|> P.fmap P.show b) | n <- ints, b <- bools]
    ),
    ( "Constructor Maybe choice is left biased",
      A.chooseWith Optional P.show P.show (Just (7 :: Int)) (Just True) P.== Just "7"
    ),
    ( "Constructor Maybe choice falls back to the right",
      A.chooseWith Optional P.show P.show (Nothing :: Maybe Int) (Just True) P.== Just "True"
    ),
    ( "Constructor Maybe choice preserves total absence",
      A.chooseWith Optional P.show P.show (Nothing :: Maybe Int) (Nothing :: Maybe Bool) P.== Nothing
    ),
    ( "Product helper needs no unit",
      combine @ApplyOnly (\n b -> if b then P.show n else "no") (1 :| [2 :: Int]) (True :| [False])
        P.== ("1" :| ["no", "2", "no"])
    ),
    ( "Choice helper needs neither product nor unit",
      choose @ChoiceOnly P.show P.show (1 :| [2 :: Int]) (True :| [False]) P.== ("1" :| ["2", "True", "False"])
    ),
    ( "Unit helpers need no functor or binary operation",
      A.pure UnitOnly (7 :: Int) P.== Just 7 P.&& A.blank @Int UnitOnly P.== Nothing
    ),
    ( "List ordering rules out an extra distributivity law",
      let together = A.liftA2 Lists ((P.+) @Int) [1, 2] (A.chooseWith Lists P.id P.id [10] [20])
          separate = A.chooseWith Lists P.id P.id (A.liftA2 Lists ((P.+) @Int) [1, 2] [10]) (A.liftA2 Lists ((P.+) @Int) [1, 2] [20])
       in together P.== [11, 21, 12, 22] P.&& separate P.== [11, 12, 21, 22] P.&& together P./= separate
    ),
    ( "The same distributivity comparison agrees for optional values",
      P.and
        [ A.liftA2 Optional ((P.+) @Int) a (A.chooseWith Optional P.id P.id b c)
            P.== A.chooseWith Optional P.id P.id (A.liftA2 Optional ((P.+) @Int) a b) (A.liftA2 Optional ((P.+) @Int) a c)
        | a <- ints,
          b <- ints,
          c <- ints
        ]
    ),
    ( "Function application preserves list function order",
      A.apply Lists [(P.+ 1), (P.* 10)] [2, 3 :: Int] P.== [3, 4, 20, 30]
    ),
    ( "Sequencing preserves list multiplicity and order",
      A.keepLeft Lists [1, 2 :: Int] [True, False] P.== [1, 1, 2, 2]
        P.&& A.keepRight Lists [1, 2 :: Int] [True, False] P.== [True, False, True, False]
    ),
    ( "Sequencing and application preserve empty list effects",
      A.keepLeft Lists [1 :: Int] ([] :: [Bool]) P.== []
        P.&& A.keepRight Lists ([] :: [Int]) [True] P.== []
        P.&& A.apply Lists ([] :: [Int -> Int]) [1] P.== []
        P.&& A.apply Lists [(P.+ 1)] ([] :: [Int]) P.== []
    ),
    ( "Same-type list choice concatenates and permits empty operands",
      P.and [A.choose Lists xs ys P.== xs P.++ ys | xs <- [[], [1, 2 :: Int]], ys <- [[], [3, 4]]]
    ),
    ( "Derived optional helpers agree with Prelude",
      P.and
        [ A.keepLeft Optional n b P.== (n P.<* b)
            P.&& A.keepRight Optional n b P.== (n P.*> b)
        | n <- ints,
          b <- bools
        ]
        P.&& P.and [A.apply Optional f n P.== (f P.<*> n) | f <- [Nothing, Just P.show], n <- ints]
        P.&& P.and [A.choose Optional n m P.== (n P.<|> m) | n <- ints, m <- ints]
    ),
    ( "Optional choice does not demand an unused fallback",
      A.choose Optional (Just (7 :: Int)) (P.error "unused fallback") P.== Just 7
    ),
    ( "Derived product helpers need no unit",
      applyAbstract @ApplyOnly ((P.+ 1) :| [(P.* 10)]) (2 :| [3 :: Int]) P.== (3 :| [4, 20, 30])
        P.&& keepLeftAbstract @ApplyOnly (1 :| [2 :: Int]) (True :| [False]) P.== (1 :| [1, 2, 2])
        P.&& keepRightAbstract @ApplyOnly (1 :| [2 :: Int]) (True :| [False]) P.== (True :| [False, True, False])
    ),
    ( "Same-type choice needs neither product nor unit",
      chooseAbstract @ChoiceOnly (1 :| [2 :: Int]) (3 :| [4]) P.== (1 :| [2, 3, 4])
    ),
    ( "Writer product and application retain noncommutative effect order",
      A.liftA2 Writer render (["left"], 7) (["right"], True) P.== (["left", "right"], "7")
        P.&& A.apply Writer (["function"], P.show) (["argument"], 7 :: Int) P.== (["function", "argument"], "7")
        P.&& A.pure Writer (7 :: Int) P.== ([], 7)
    ),
    ( "Writer sequencing retains both logs when discarding either result",
      A.keepLeft Writer (["left"], 7 :: Int) (["right"], True) P.== (["left", "right"], 7)
        P.&& A.keepRight Writer (["left"], 7 :: Int) (["right"], True) P.== (["left", "right"], True)
    ),
    ( "ZipList combines matching positions and stops at the shorter input",
      A.liftA2 Zipped render (P.ZipList [1, 2, 3]) (P.ZipList [True, False]) P.== P.ZipList ["1", "no"]
        P.&& A.apply Zipped (P.ZipList [P.show, \_ -> "second"]) (P.ZipList [7, 8, 9 :: Int]) P.== P.ZipList ["7", "second"]
        P.&& A.liftA2 Zipped render (P.ZipList []) (P.ZipList [True]) P.== P.ZipList []
    ),
    ( "ZipList pure repeats indefinitely (observed through a finite prefix)",
      P.take 10 (P.getZipList (A.pure Zipped (7 :: Int))) P.== P.replicate 10 7
    ),
    ( "ZipList sequencing retains positional length",
      A.keepLeft Zipped (P.ZipList [1, 2, 3 :: Int]) (P.ZipList [True, False]) P.== P.ZipList [1, 2]
        P.&& A.keepRight Zipped (P.ZipList [1 :: Int]) (P.ZipList [True, False]) P.== P.ZipList [True]
    )
  ]
