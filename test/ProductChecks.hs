module ProductChecks (checks) where

import AdjunctionChecks (OnlyTrue (..), OnlyUnit (..), ToTrue, ToUnit)
import Cats
import Data.Type.Equality ((:~:) (Refl))
import Prelude (Bool (..), Int, Maybe (..), String)
import Prelude qualified as P

type Lists = Constructor []

type Optional = Constructor Maybe

type Parallel = Lists *** Optional

type Pointwise = Lists &&& Optional

parallelGrouping :: (Lists *** Optional *** Lists) :~: (Lists *** (Optional *** Lists))
parallelGrouping = Refl

pointwiseGrouping :: (Lists &&& Optional &&& Lists) :~: (Lists &&& (Optional &&& Lists))
pointwiseGrouping = Refl

ints :: [Int]
ints = [-3 .. 3]

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs f g = P.all (\x -> f x P.== g x) xs

checks :: [(String, Bool)]
checks =
  [ ( "Parallel product maps different endpoint types",
      case map Parallel ((P.show :: Int -> String) :×: P.fromEnum @Bool) of
        l :×: r -> l [1, 2] P.== ["1", "2"] P.&& r (Just True) P.== Just 1
    ),
    ( "Parallel product preserves identities",
      case map Parallel (identity (type '(Int, Bool))) of
        l :×: r -> l ints P.== ints P.&& r (Just True) P.== Just True
    ),
    ( "Parallel product preserves composition order",
      let first = (P.+ 1) :×: (P.* 2)
          second = (P.* 3) :×: (P.+ 5)
       in case (map Parallel (second ∘ first), map Parallel second ∘ map Parallel first) of
            (l :×: r, l' :×: r') ->
              l ints P.== l' ints
                P.&& l ints P.== P.map (\n -> 3 P.* (n P.+ 1)) ints
                P.&& r (Just (7 :: Int)) P.== r' (Just 7)
                P.&& r (Just 7) P.== Just 19
    ),
    ( "Pointwise product shares the source arrow",
      case map Pointwise (P.show :: Int -> String) of
        l :×: r -> l [1, 2] P.== ["1", "2"] P.&& r (Just 3) P.== Just "3"
    ),
    ( "Pointwise product preserves identities",
      case map Pointwise (identity Int) of
        l :×: r -> l ints P.== ints P.&& r (Just 7) P.== Just 7
    ),
    ( "Pointwise product preserves composition order",
      case (map Pointwise ((P.* 3) ∘ (P.+ 1)), map Pointwise (P.* 3) ∘ map Pointwise (P.+ 1)) of
        (l :×: r, l' :×: r') ->
          l ints P.== l' ints
            P.&& r (Just 7) P.== r' (Just 7)
            P.&& r (Just 7) P.== Just (24 :: Int)
    ),
    ( "Projection functors recover parallel components",
      map (FstFunctor • Parallel) ((P.show :: Int -> String) :×: P.not) [1, 2] P.== ["1", "2"]
        P.&& map (SndFunctor • Parallel) ((P.show :: Int -> String) :×: P.not) (Just True) P.== Just False
    ),
    ( "Projection functors recover pointwise components",
      map (FstFunctor • Pointwise) (P.show :: Int -> String) [1, 2] P.== ["1", "2"]
        P.&& map (SndFunctor • Pointwise) (P.show :: Int -> String) (Just 3) P.== Just "3"
    ),
    ( "Pairing projections reconstructs the original arrow",
      case map (FstFunctor &&& SndFunctor) ((P.+ 2) :×: P.not) of
        l :×: r -> sameOn ints l (P.+ 2) P.&& sameOn [False, True] r P.not
    ),
    ( "Parallel product supports different category kinds",
      case map (ToUnit *** ToTrue) (TArrow (P.+ 1) :×: UArrow (P.* 3)) of
        UArrow l :×: TArrow r -> sameOn ints l (P.+ 1) P.&& sameOn ints r (P.* 3)
    ),
    ( "Pointwise product supports different target kinds",
      case map ((Id @OnlyTrue) &&& ToUnit) (TArrow (P.+ 3)) of
        TArrow l :×: UArrow r -> sameOn ints l (P.+ 3) P.&& sameOn ints r (P.+ 3)
    ),
    ( "Projections retain constrained object evidence",
      case (map (FstFunctor @OnlyTrue @OnlyUnit) (identity (type '( 'True, '()))), map (SndFunctor @OnlyTrue @OnlyUnit) (identity (type '( 'True, '())))) of
        (TArrow l, UArrow r) -> sameOn ints l P.id P.&& sameOn ints r P.id
    ),
    ( "Functor product operators associate to the right",
      case (parallelGrouping, pointwiseGrouping) of (Refl, Refl) -> True
    )
  ]
