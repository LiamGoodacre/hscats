module DayChecks where

import Cats
import Cats.Day
import Data.Type.Equality (type (~))
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type List = Constructor []

type ProductDay = Day₁ @Types @Types (∧)

type SumDay = Day₁ @Types @Types (∨)

productValues :: forall z. DataDay (∧) List List z -> [z]
productValues = append ProductDay List $$ z

sumValues :: forall z. DataDay (∨) List List z -> [z]
sumValues = append SumDay List $$ z

productRightValues :: DataDay (∧) List (Day (∧) List List) z -> [z]
productRightValues (DataDayTypes f xs inner) = [f (x, y) | x <- xs, y <- productValues inner]

productLeftValues :: DataDay (∧) (Day (∧) List List) List z -> [z]
productLeftValues (DataDayTypes f inner ys) = [f (x, y) | x <- productValues inner, y <- ys]

sumRightValues :: DataDay (∨) List (Day (∨) List List) z -> [z]
sumRightValues (DataDayTypes f xs inner) =
  P.map (f ∘ P.Left) xs P.++ P.map (f ∘ P.Right) (sumValues inner)

sumLeftValues :: DataDay (∨) (Day (∨) List List) List z -> [z]
sumLeftValues (DataDayTypes f inner ys) =
  P.map (f ∘ P.Left) (sumValues inner) P.++ P.map (f ∘ P.Right) ys

-- Different hidden types and non-identity combining arrows ensure that the
-- associators must transport the computation, not just rearrange constructors.
productRight :: DataDay (∧) List (Day (∧) List List) Int
productRight =
  DataDayTypes
    (\(x, y) -> 1000 P.* x P.+ y)
    [1, 2]
    (DataDayTypes (\(b, c) -> if b then P.fromEnum c else P.negate (P.fromEnum c)) [True, False] ['a', 'b'])

productLeft :: DataDay (∧) (Day (∧) List List) List Int
productLeft =
  DataDayTypes
    (\(x, c) -> x P.+ P.fromEnum c)
    (DataDayTypes (\(n, b) -> if b then 2 P.* n else n P.+ 7) [1, 3] [True, False])
    ['a', 'c']

sumRight :: DataDay (∨) List (Day (∨) List List) Int
sumRight =
  DataDayTypes
    (P.either (P.* 1000) (P.+ 10))
    [1, 2]
    (DataDayTypes (P.either (\b -> if b then 7 else 9) P.fromEnum) [True, False] ['a', 'b'])

sumLeft :: DataDay (∨) (Day (∨) List List) List Int
sumLeft =
  DataDayTypes
    (P.either (P.+ 10) P.fromEnum)
    (DataDayTypes (P.either (P.* 1000) (\b -> if b then 7 else 9)) [1, 2] [True, False])
    ['a', 'b']

-- The source category from the generic associativity counterexample. Addition
-- is commutative, so Tensor is a lawful bifunctor with identity associators.
data Add :: CATEGORY () where
  Add :: Int -> Add '() '()

type instance Obj Add x = x ~ '()

instance Semigroupoid Add where
  Add a ∘ Add b = Add (a P.+ b)

instance Category Add where
  identity _ = Add 0

type data Tensor :: (Add × Add) --> Add

type instance Act Tensor p = '()

instance Functor Tensor where
  map _ (Add a :×: Add b) = Add (a P.+ b)

instance Associative Tensor where
  lassoc _ _ _ _ = Add 0
  rassoc _ _ _ _ = Add 0

type Unit = Δ' @Types @Add ()

type CounterexampleDay = Day₁ @Add @Types Tensor

counterexample :: DataDay Tensor Unit (Day Tensor Unit Unit) '()
counterexample = DataDayTypes (Add 2) () (DataDayTypes (Add 3) () ())

observeCounterexample :: DataDay Tensor Unit (Day Tensor Unit Unit) '() -> (Int, Int)
observeCounterexample (DataDayTypes (Add outer) () (DataDayTypes (Add inner) () ())) = (outer, inner)

checks :: [(String, Bool)]
checks =
  [ ( "Day product left associator preserves interpretation",
      productLeftValues ((lassoc ProductDay List List List $$ Int) productRight)
        P.== productRightValues productRight
    ),
    ( "Day product right associator preserves interpretation",
      productRightValues ((rassoc ProductDay List List List $$ Int) productLeft)
        P.== productLeftValues productLeft
    ),
    ( "Day product right-associated round trip",
      productRightValues ((rassoc ProductDay List List List ∘ lassoc ProductDay List List List $$ Int) productRight)
        P.== productRightValues productRight
    ),
    ( "Day product left-associated round trip",
      productLeftValues ((lassoc ProductDay List List List ∘ rassoc ProductDay List List List $$ Int) productLeft)
        P.== productLeftValues productLeft
    ),
    ( "Day coproduct left associator preserves all branches",
      sumLeftValues ((lassoc SumDay List List List $$ Int) sumRight) P.== [1000, 2000, 17, 19, 107, 108]
    ),
    ( "Day coproduct right associator preserves all branches",
      sumRightValues ((rassoc SumDay List List List $$ Int) sumLeft) P.== [1010, 2010, 17, 19, 97, 98]
    ),
    ( "Day coproduct right-associated round trip",
      sumRightValues ((rassoc SumDay List List List ∘ lassoc SumDay List List List $$ Int) sumRight)
        P.== sumRightValues sumRight
    ),
    ( "Day coproduct left-associated round trip",
      sumLeftValues ((lassoc SumDay List List List ∘ rassoc SumDay List List List $$ Int) sumLeft)
        P.== sumLeftValues sumLeft
    ),
    ( "Day product monoidal instance remains available",
      ((idl @_ @ProductDay @List ∘ coidl @_ @ProductDay @List) $$ Int) [1, 2] P.== [1, 2]
    ),
    ( "Day coproduct monoidal instance remains available",
      ((idr @_ @SumDay @List ∘ coidr @_ @SumDay @List) $$ Int) [1, 2] P.== [1, 2]
    ),
    ( "Generic Day retains observable intermediate arrows",
      observeCounterexample counterexample P.== (2, 3)
    ),
    ( "Generic Day mapping remains available",
      observeCounterexample (map (Day Tensor Unit (Day Tensor Unit Unit)) (Add 4) counterexample) P.== (6, 3)
    )
  ]
