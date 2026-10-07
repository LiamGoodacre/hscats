module DayConversionChecks (checks) where

import AdjunctionChecks (Env, Reader)
import Cats
import Data.Maybe qualified as Maybe
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type List = Constructor []
type Optional = Constructor P.Maybe
type Pair = Env Bool

type ProductDay = Day (∧) Pair List
type Composition = Pair • List

forward :: ProductDay ~> Composition
forward = dayToComposeTypes

backward :: Composition ~> ProductDay
backward = composeToDayTypes @Pair @List @(Reader Bool)

lists :: [[Int]]
lists = [[], [0], [1, 2], [-3, 0, 4]]

compositions :: [Act Composition Int]
compositions = [(xs, b) | xs <- lists, b <- [False, True]]

days :: [Act ProductDay Int]
days =
  [ DataDayTypes (\(x, c) -> x P.* 10 P.+ P.fromEnum c) (n, b) cs
  | n <- [-2, 3], b <- [False, True], cs <- [[], ['a'], ['b', 'c']]
  ]

-- Independent eliminations: one retains the environment and result order;
-- the other interprets into the ordinary list Day monoid via natural maps.
observe :: DataDay (∧) (Env s) List a -> ([a], s)
observe (DataDayTypes k (x, s) ys) = (P.map (\y -> k (x, y)) ys, s)

forgetEnv :: Pair ~> List
forgetEnv = EXP \_ (a, _) -> [a]

asList :: ProductDay ~> List
asList = append (Day₁ (∧)) List ∘ map (Day₁ (∧)) (forgetEnv :×: identity List)

changeEnv :: Pair ~> Env String
changeEnv = EXP \_ (a, b) -> (a, if b then "on" else "off")

first :: List ~> Optional
first = EXP \_ -> Maybe.listToMaybe

dayChange :: ProductDay ~> Day (∧) (Env String) Optional
dayChange = map (Day₁ (∧)) (changeEnv :×: first)

composeChange :: Composition ~> (Env String • Optional)
composeChange = map Composing (changeEnv :×: first)

observeOptional :: DataDay (∧) (Env String) Optional a -> (P.Maybe a, String)
observeOptional (DataDayTypes k (x, s) y) = (P.fmap (\z -> k (x, z)) y, s)

checks :: [(String, Bool)]
checks =
  [ ( "Day to composition preserves combination and environment",
      P.all (\d -> (forward $$ Int) d P.== observe d) days
    ),
    ( "Composition to Day preserves empty and nonempty inputs",
      P.all (\c -> observe ((backward $$ Int) c) P.== c) compositions
    ),
    ( "Composition to Day to composition round trip",
      P.all (\c -> ((forward ∘ backward) $$ Int) c P.== c) compositions
    ),
    ( "Day round trip preserves environment and ordered results",
      P.all (\d -> observe (((backward ∘ forward) $$ Int) d) P.== observe d) days
    ),
    ( "Day round trip agrees under a list monoid interpretation",
      P.all (\d -> ((asList ∘ backward ∘ forward) $$ Int) d P.== (asList $$ Int) d) days
    ),
    ( "Day to composition is natural in the result",
      P.all
        (\d -> map Composition P.show ((forward $$ Int) d)
          P.== (forward $$ String) (map ProductDay P.show d))
        days
    ),
    ( "Composition to Day is natural in the result",
      P.all
        (\c -> observe (map ProductDay P.show ((backward $$ Int) c))
          P.== observe ((backward $$ String) (map Composition P.show c)))
        compositions
    ),
    ( "Day to composition is natural in both functor arguments",
      P.all
        (\d -> ((composeChange ∘ forward) $$ Int) d
          P.== ((dayToComposeTypes @(Env String) @Optional ∘ dayChange) $$ Int) d)
        days
    ),
    ( "Composition to Day is natural in both functor arguments",
      P.all
        (\c -> observeOptional (((dayChange ∘ backward) $$ Int) c)
          P.== observeOptional (((composeToDayTypes @(Env String) @Optional @(Reader String) ∘ composeChange) $$ Int) c))
        compositions
    ),
    ( "Day to composition also supports functors without a right adjoint",
      (dayToComposeTypes @List @Optional $$ Int)
        (DataDayTypes (\(n, b) -> if b then n P.* 2 else n) [1, 3] (P.Just True))
        P.== [P.Just 2, P.Just 6]
    )
  ]
