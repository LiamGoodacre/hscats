module ApplicativeHelpersChecks (checks) where

import ApplicativeChecks (ChoiceOnly)
import Cats
import Cats.Applicative qualified as A
import Control.Applicative qualified as P
import Data.List.NonEmpty (NonEmpty (..))
import Prelude (Bool (..), Int, Maybe (..), String)
import Prelude qualified as P

type Lists = Constructor []

type Optional = Constructor Maybe

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
  lift0 = EXP \_ -> Just

instance A.Lift0 (∨) UnitOnly where
  lift0 = EXP \_ () -> Nothing

-- Keep these constraints abstract to check the advertised helper requirements.
combine :: forall (f :: Types --> Types) a b c. (A.Apply f) => (a -> b -> c) -> Act f a -> Act f b -> Act f c
combine = A.liftA2 f

choose :: forall (f :: Types --> Types) a b c. (A.Alt f) => (a -> c) -> (b -> c) -> Act f a -> Act f b -> Act f c
choose = A.chooseWith f

ints :: [Maybe Int]
ints = [Nothing, Just (-2), Just 7]

bools :: [Maybe Bool]
bools = [Nothing, Just False, Just True]

render :: Int -> Bool -> String
render n b = if b then P.show n else "no"

checks :: [(String, Bool)]
checks =
  [ ("Constructor list pure", A.pure Lists (7 :: Int) P.== [7]),
    ("Constructor list empty", A.empty @Int Lists P.== []),
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
    ("Constructor Maybe empty", A.empty @Int Optional P.== Nothing),
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
      A.pure UnitOnly (7 :: Int) P.== Just 7 P.&& A.empty @Int UnitOnly P.== Nothing
    ),
    ( "Example List delegates the ordinary constructor behavior",
      A.pure A.List (7 :: Int) P.== A.pure Lists 7
        P.&& A.empty @Int A.List P.== A.empty @Int Lists
        P.&& A.liftA2 A.List render [1, 2] [False, True] P.== A.liftA2 Lists render [1, 2] [False, True]
        P.&& A.chooseWith A.List P.show P.show [1, 2 :: Int] [False, True]
          P.== A.chooseWith Lists P.show P.show [1, 2 :: Int] [False, True]
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
    )
  ]
