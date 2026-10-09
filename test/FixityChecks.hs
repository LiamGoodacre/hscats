module FixityChecks (checks) where

import Cats
import Data.Type.Equality ((:~:) (Refl))
import Prelude (Bool (..), Int, Maybe, String)
import Prelude qualified as P

type F = Constructor []
type G = Constructor Maybe
type H = Id @Types

-- Leave the left sides unparenthesized: these witnesses check the parser.
compositionGrouping :: (F • G • H) :~: (F • (G • H))
compositionGrouping = Refl

productGrouping :: (Types × Types × Types) :~: (Types × (Types × Types))
productGrouping = Refl

exponentialGrouping :: (Types ^ Types ^ Types) :~: (Types ^ (Types ^ Types))
exponentialGrouping = Refl

arrowPrecedence :: (Types × Types --> Types ^ Types) :~: ((Types × Types) --> (Types ^ Types))
arrowPrecedence = Refl

naturalPrecedence :: (F • G ~> H) :~: ((F • G) ~> H)
naturalPrecedence = Refl

profunctorPrecedence :: (Types × Types -/-> Types) :~: PROFUNCTOR Types (Types × Types)
profunctorPrecedence = Refl

adjunctionPrecedence :: (F • G ⊣ H) :~: ((F • G) ⊣ H)
adjunctionPrecedence = Refl

tensorApplication :: ((Int ☼ Bool) (∧)) :~: (Int, Bool)
tensorApplication = Refl

mapFromObject :: forall f a b. (f ∈ Types ^ Types) => (a -> b) -> Act f a -> Act f b
mapFromObject = map f

reverseList, dropFirst :: F ~> F
reverseList = EXP \_ -> P.reverse
dropFirst = EXP \_ -> P.drop 1

nested :: Curry₁ (∧) ~> Curry₁ (∧)
nested = identity (Curry₁ (∧))

threeArrows :: (Types × (Types × Types)) '(Int, '(Bool, String)) '(String, '(Bool, Int))
threeArrows = P.show ∘ (P.+ 1) :×: P.not :×: P.length

checks :: [(String, Bool)]
checks =
  [ ( "Composition, product, and exponentiation group to the right",
      case (compositionGrouping, productGrouping, exponentialGrouping) of
        (Refl, Refl, Refl) -> True
    ),
    ( "Arrow, transformation, adjunction, and tensor precedence",
      case (arrowPrecedence, naturalPrecedence, profunctorPrecedence, adjunctionPrecedence, tensorApplication) of
        (Refl, Refl, Refl, Refl, Refl) -> True
    ),
    ("Membership binds below functor categories", mapFromObject @F P.show [1, 2 :: Int] P.== ["1", "2"]),
    ("Compose transformations before selecting a component", (dropFirst ∘ reverseList $$ Int) [1, 2, 3] P.== [2, 1]),
    ("Repeated component selection groups to the left", (nested $$ Int $$ Bool) (7, True) P.== (7, True)),
    ( "Compose arrows before forming right-associated products",
      case threeArrows of
        f :×: (g :×: h) -> f 7 P.== "8" P.&& g True P.== False P.&& h "abc" P.== 3
    ),
    ("Categorical and Prelude composition share a fixity", (P.show ∘ P.length P.. P.reverse) ("abc" :: String) P.== "3"),
    ("Monoid append and Prelude append share a fixity", [1] <> [2] P.<> [3 :: Int] P.== [1, 2, 3])
  ]
