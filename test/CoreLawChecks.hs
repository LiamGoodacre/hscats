module CoreLawChecks (checks) where

import AdjunctionChecks (OnlyTrue (..), OnlyUnit (..), ToUnit)
import Cats
import DayChecks (Add (..))
import Prelude (Bool, Int, String)
import Prelude qualified as P

-- Add has one valid object, '(), and integer arrows composed by addition.
-- These functors make non-identity source arrows observable in Types.
type data Shift :: Add --> Types

type instance Act Shift a = Int

instance Functor Shift where
  map _ (Add n) = (P.+ n)

type data K :: Add --> Add

type instance Act K a = '()

instance Functor K where
  map _ _ = Add 0

translate :: Int -> Shift ~> Shift
translate n = EXP \_ -> (P.+ n)

constantArrow :: Int -> K ~> K
constantArrow n = EXP \_ -> Add n

-- A deliberately unlawful component family. Its type is accepted by EXP,
-- but the naturality square for Add 1 does not commute.
doubling :: Shift ~> Shift
doubling = EXP \_ -> (P.* 2)

maybeToList :: Constructor P.Maybe ~> Constructor []
maybeToList = EXP \_ -> \case
  P.Nothing -> []
  P.Just a -> [a]

arrowValue :: Add '() '() -> Int
arrowValue (Add n) = n

values :: [Int]
values = [-3 .. 3]

checks :: [(String, Bool)]
checks =
  [ ( "Category identities with a constrained object",
      P.and
        [ arrowValue (identity (type '()) ∘ Add n) P.== n
            P.&& arrowValue (Add n ∘ identity (type '())) P.== n
        | n <- values
        ]
    ),
    ( "Category associativity with nontrivial arrows",
      P.and
        [ arrowValue ((Add a ∘ Add b) ∘ Add c) P.== arrowValue (Add a ∘ (Add b ∘ Add c))
        | a <- values,
          b <- values,
          c <- values
        ]
    ),
    ( "Shift functor identity",
      P.all (\x -> map Shift (identity (type '())) x P.== x) values
    ),
    ( "Shift functor composition",
      P.and
        [ map Shift (Add a ∘ Add b) x P.== (map Shift (Add a) ∘ map Shift (Add b)) x
        | a <- values,
          b <- values,
          x <- values
        ]
    ),
    ( "K functor identity and composition",
      arrowValue (map K (identity (type '()))) P.== 0
        P.&& P.and
          [ arrowValue (map K (Add a ∘ Add b)) P.== arrowValue (map K (Add a) ∘ map K (Add b))
          | a <- values,
            b <- values
          ]
    ),
    ( "Translation component families are natural",
      P.and
        [ (map Shift (Add n) ∘ (translate k $$ ())) x
            P.== ((translate k $$ ()) ∘ map Shift (Add n)) x
        | n <- values,
          k <- values,
          x <- values
        ]
    ),
    ( "K component families are natural",
      P.and
        [ arrowValue (map K (Add n) ∘ (constantArrow k $$ ()))
            P.== arrowValue ((constantArrow k $$ ()) ∘ map K (Add n))
        | n <- values,
          k <- values
        ]
    ),
    ( "Composing preserves identity on lawful transformations",
      P.all
        (\x -> (map Composing (identity Shift :×: identity K) $$ ()) x P.== x)
        values
    ),
    ( "Composing preserves composition on lawful transformations",
      P.and
        [ let first = translate a :×: constantArrow b
              second = translate c :×: constantArrow d
           in (map Composing (second ∘ first) $$ ()) x
                P.== ((map Composing second ∘ map Composing first) $$ ()) x
        | a <- [-2, 3],
          b <- [-1, 2],
          c <- [1, 4],
          d <- [-3, 2],
          x <- values
        ]
    ),
    ( "EXP admits a non-natural component family",
      let after = (map Shift (Add 1) ∘ (doubling $$ ())) 0
          before = ((doubling $$ ()) ∘ map Shift (Add 1)) 0
       in (after, before) P.== (1, 2)
    ),
    ( "Non-natural components break Composing's composition law",
      let pair = doubling :×: constantArrow 1
          together = (map Composing (pair ∘ pair) $$ ()) 0
          separately = ((map Composing pair ∘ map Composing pair) $$ ()) 0
       in (together, separately) P.== (2, 3)
    ),
    ( "Eval preserves identity with a constrained source object",
      P.all (\x -> map (Eval @Add @Types) (identity Shift :×: identity (type '())) x P.== x) values
    ),
    ( "Eval preserves composition for natural transformations",
      P.and
        [ let first = translate a :×: Add b
              second = translate c :×: Add d
           in map Eval (second ∘ first) x P.== (map Eval second ∘ map Eval first) x
        | a <- [-2, 3],
          b <- [-1, 2],
          c <- [1, 4],
          d <- [-3, 2],
          x <- values
        ]
    ),
    ( "Non-natural components break Eval's composition law",
      let pair = doubling :×: Add 1
       in (map Eval (pair ∘ pair) 0, (map Eval pair ∘ map Eval pair) 0) P.== (2, 3)
    ),
    ( "Eval changes the functor and argument types together",
      P.all
        ( \x ->
            map Eval (maybeToList :×: (P.show :: Int -> String)) x
              P.== (maybeToList $$ String) (map (type (Constructor P.Maybe)) P.show x)
        )
        [P.Nothing, P.Just 7, P.Just (-2)]
        P.&& map Eval (maybeToList :×: (P.show :: Int -> String)) (P.Just 7) P.== ["7"]
    ),
    ( "Eval supports a constrained non-Types codomain",
      case map Eval (identity ToUnit :×: TArrow (P.* 3)) of
        UArrow f -> P.all (\n -> f n P.== 3 P.* n) values
    )
  ]
