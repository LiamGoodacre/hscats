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

-- The two paths around the pentagon, from (((f g) h) i) to f (g (h i)).
pentagonShort,
  pentagonLong ::
    forall (o :: BINARY_OP Types).
    (Associative o) =>
    Day o (Day o (Day o List List) List) List ~> Day o List (Day o List (Day o List List))
pentagonShort =
  rassoc (Day₁ o) List List (Day o List List)
    ∘ rassoc (Day₁ o) (Day o List List) List List
pentagonLong =
  map (Day₁ o) (identity List :×: rassoc (Day₁ o) List List List)
    ∘ rassoc (Day₁ o) List (Day o List List) List
    ∘ map (Day₁ o) (rassoc (Day₁ o) List List List :×: identity List)

-- The triangle compares eliminating the unit before and after reassociation.
triangleDirect,
  triangleViaAssoc ::
    forall (o :: BINARY_OP Types).
    (Associative o, Monoidal (Day₁ @Types @Types o)) =>
    Day o (Day o List (MonoidalEmpty (Day₁ o))) List ~> Day o List List
triangleDirect = map (Day₁ o) (idr @_ @(Day₁ o) @List :×: identity List)
triangleViaAssoc =
  map (Day₁ o) (identity List :×: idl @_ @(Day₁ o) @List)
    ∘ rassoc (Day₁ o) List (MonoidalEmpty (Day₁ o)) List

productFour :: DataDay (∧) (Day (∧) (Day (∧) List List) List) List Int
productFour = DataDayTypes (\(x, y) -> 10 P.* x P.+ y) productLeft [0, 5]

productFourValues :: DataDay (∧) List (Day (∧) List (Day (∧) List List)) z -> [z]
productFourValues (DataDayTypes f xs inner) = [f (x, y) | x <- xs, y <- productRightValues inner]

sumFour :: DataDay (∨) (Day (∨) (Day (∨) List List) List) List Int
sumFour = DataDayTypes (P.either (P.+ 100) P.fromEnum) sumLeft [False, True]

sumFourValues :: DataDay (∨) List (Day (∨) List (Day (∨) List List)) z -> [z]
sumFourValues (DataDayTypes f xs inner) =
  P.map (f ∘ P.Left) xs P.++ P.map (f ∘ P.Right) (sumRightValues inner)

type Blank = MonoidalEmpty SumDay

productUnitLeft :: DataDay (∧) Id List Int
productUnitLeft = DataDayTypes (\(x, b) -> if b then x else x P.+ 1) 7 [True, False]

productUnitRight :: DataDay (∧) List Id Int
productUnitRight = DataDayTypes (\(x, s) -> x P.+ P.length s) [1, 3] "unit"

sumUnitLeft :: DataDay (∨) Blank List Int
sumUnitLeft = DataDayTypes (P.either (P.fromEnum :: P.Char -> Int) (P.* 3)) () [2, 4]

sumUnitRight :: DataDay (∨) List Blank Int
sumUnitRight = DataDayTypes (P.either (P.* 10) (P.fromEnum :: P.Char -> Int)) [1, 3] ()

productUnitLeftValues :: DataDay (∧) Id List z -> [z]
productUnitLeftValues (DataDayTypes f x ys) = [f (x, y) | y <- ys]

productUnitRightValues :: DataDay (∧) List Id z -> [z]
productUnitRightValues (DataDayTypes f xs y) = [f (x, y) | x <- xs]

sumUnitLeftValues :: DataDay (∨) Blank List z -> [z]
sumUnitLeftValues (DataDayTypes f () ys) = P.map (f ∘ P.Right) ys

sumUnitRightValues :: DataDay (∨) List Blank z -> [z]
sumUnitRightValues (DataDayTypes f xs ()) = P.map (f ∘ P.Left) xs

productTriangle :: DataDay (∧) (Day (∧) List Id) List Int
productTriangle = DataDayTypes (\(x, b) -> if b then 2 P.* x else x P.- 5) productUnitRight [True, False]

sumTriangle :: DataDay (∨) (Day (∨) List Blank) List Int
sumTriangle = DataDayTypes (P.either (P.+ 100) P.fromEnum) sumUnitRight [True, False]

coherenceChecks :: [(String, Bool)]
coherenceChecks =
  [ ( "Day product pentagon",
      let short = productFourValues ((pentagonShort @(∧) $$ Int) productFour)
          long = productFourValues ((pentagonLong @(∧) $$ Int) productFour)
          expected = [10 P.* x P.+ y | x <- productLeftValues productLeft, y <- [0, 5]]
       in short P.== expected P.&& long P.== expected
    ),
    ( "Day coproduct pentagon",
      let short = sumFourValues ((pentagonShort @(∨) $$ Int) sumFour)
          long = sumFourValues ((pentagonLong @(∨) $$ Int) sumFour)
          expected = P.map (P.+ 100) (sumLeftValues sumLeft) P.++ [0, 1]
       in short P.== expected P.&& long P.== expected
    ),
    ( "Day product triangle",
      productValues ((triangleDirect @(∧) $$ Int) productTriangle) P.== [10, 0, 14, 2]
        P.&& productValues ((triangleViaAssoc @(∧) $$ Int) productTriangle) P.== [10, 0, 14, 2]
    ),
    ( "Day coproduct triangle",
      sumValues ((triangleDirect @(∨) $$ Int) sumTriangle) P.== [110, 130, 1, 0]
        P.&& sumValues ((triangleViaAssoc @(∨) $$ Int) sumTriangle) P.== [110, 130, 1, 0]
    ),
    ( "Day product left unit insertion then elimination",
      P.all (\xs -> ((idl @_ @ProductDay @List ∘ coidl @_ @ProductDay @List) $$ Int) xs P.== xs) [[], [1], [1, 2]]
    ),
    ( "Day product right unit insertion then elimination",
      P.all (\xs -> ((idr @_ @ProductDay @List ∘ coidr @_ @ProductDay @List) $$ Int) xs P.== xs) [[], [1], [1, 2]]
    ),
    ( "Day coproduct left unit insertion then elimination",
      P.all (\xs -> ((idl @_ @SumDay @List ∘ coidl @_ @SumDay @List) $$ Int) xs P.== xs) [[], [1], [1, 2]]
    ),
    ( "Day coproduct right unit insertion then elimination",
      P.all (\xs -> ((idr @_ @SumDay @List ∘ coidr @_ @SumDay @List) $$ Int) xs P.== xs) [[], [1], [1, 2]]
    ),
    ( "Day product left unit elimination then insertion",
      productUnitLeftValues (((coidl @_ @ProductDay @List ∘ idl @_ @ProductDay @List) $$ Int) productUnitLeft) P.== [7, 8]
    ),
    ( "Day product right unit elimination then insertion",
      productUnitRightValues (((coidr @_ @ProductDay @List ∘ idr @_ @ProductDay @List) $$ Int) productUnitRight) P.== [5, 7]
    ),
    ( "Day coproduct left unit elimination then insertion",
      sumUnitLeftValues (((coidl @_ @SumDay @List ∘ idl @_ @SumDay @List) $$ Int) sumUnitLeft) P.== [6, 12]
    ),
    ( "Day coproduct right unit elimination then insertion",
      sumUnitRightValues (((coidr @_ @SumDay @List ∘ idr @_ @SumDay @List) $$ Int) sumUnitRight) P.== [10, 30]
    ),
    ( "Day Applicative unit uses the library instance",
      (empty ProductDay List $$ Int) 7 P.== [7]
    ),
    ( "Day Alternative unit uses the library instance",
      (empty SumDay List $$ Int) () P.== []
    ),
    ( "Day product with an empty argument",
      productValues (DataDayTypes (P.uncurry ((P.+) @Int)) [] [1, 2]) P.== []
    ),
    ( "Day coproduct with an empty argument",
      sumValues (DataDayTypes (P.either ((P.+ 1) :: Int -> Int) (P.* 10)) [] [1, 2]) P.== [10, 20]
    )
  ]

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

type Numbers = Δ' @Types @Add Int

numberPair :: DataDay Tensor Numbers Numbers '()
numberPair = DataDayTypes (Add 5) 2 7

observeNumberPair :: DataDay Tensor Numbers Numbers '() -> (Int, Int, Int)
observeNumberPair (DataDayTypes (Add arrow) x y) = (arrow, x, y)

scale, shift :: Numbers ~> Numbers
scale = EXP \_ -> (P.* 2)
shift = EXP \_ -> (P.+ 3)

genericChecks :: [(String, Bool)]
genericChecks =
  [ ( "Generic Day functor identity",
      observeCounterexample (map (Day Tensor Unit (Day Tensor Unit Unit)) (identity ()) counterexample) P.== (2, 3)
    ),
    ( "Generic Day functor composition",
      let step = map (Day Tensor Unit (Day Tensor Unit Unit))
       in observeCounterexample (step (Add 4 ∘ Add 7) counterexample) P.== (13, 3)
            P.&& observeCounterexample (step (Add 4) (step (Add 7) counterexample)) P.== (13, 3)
    ),
    ( "Generic Day bifunctor identity",
      observeNumberPair ((map CounterexampleDay (identity Numbers :×: identity Numbers) $$ ()) numberPair) P.== (5, 2, 7)
    ),
    ( "Generic Day bifunctor composition",
      let first = shift :×: scale
          second = scale :×: shift
          combined = map CounterexampleDay (second ∘ first) $$ ()
          separate = (map CounterexampleDay second ∘ map CounterexampleDay first) $$ ()
       in observeNumberPair (combined numberPair) P.== (5, 10, 17)
            P.&& observeNumberPair (separate numberPair) P.== (5, 10, 17)
    )
  ]

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
    ( "Generic Day retains observable intermediate arrows",
      observeCounterexample counterexample P.== (2, 3)
    ),
    ( "Generic Day mapping remains available",
      observeCounterexample (map (Day Tensor Unit (Day Tensor Unit Unit)) (Add 4) counterexample) P.== (6, 3)
    )
  ]
    P.++ coherenceChecks
    P.++ genericChecks
