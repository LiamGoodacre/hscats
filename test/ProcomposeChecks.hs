module ProcomposeChecks (checks) where

import Cats
import Data.Type.Equality (type (~))
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type Arrows = Procompose (Hom Types) (Hom Types)

-- The intermediate type differs from both endpoints.
parity :: DataProcompose (Hom Types) (Hom Types) Int String
parity = MkProcompose @Bool (\b -> if b then "even" else "odd") P.even

runArrows :: DataProcompose (Hom Types) (Hom Types) i j -> i -> j
runArrows (MkProcompose outer inner) = outer ∘ inner

numeric :: DataProcompose (Hom Types) (Hom Types) Int Int
numeric = MkProcompose @Int (\n -> n P.* n P.+ 2) (P.subtract 3)

firstStep, secondStep :: (Op Types × Types) '(Int, Int) '(Int, Int)
firstStep = OP (P.+ 1) :×: (P.* 2)
secondStep = OP (P.* 3) :×: (P.+ 5)

ints :: [Int]
ints = [-3 .. 3]

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn samples f g = P.all (\x -> f x P.== g x) samples

type Nested = Procompose (Hom Types) Arrows

nested :: DataProcompose (Hom Types) Arrows Int String
nested = MkProcompose @String ("parity: " P.++) parity

runNested :: DataProcompose (Hom Types) Arrows i j -> i -> j
runNested (MkProcompose outer inner) = outer ∘ runArrows inner

arrowChecks :: [(String, Bool)]
arrowChecks =
  [ ( "Procompose constructs a pair of composable arrows",
      P.map (runArrows parity) [0, 1, 2, 3] P.== ["even", "odd", "even", "odd"]
    ),
    ( "Procompose functor identity",
      sameOn ints (runArrows (map Arrows (identity (type '(Int, String))) parity)) (runArrows parity)
    ),
    ( "Procompose maps both endpoints to different types",
      let changed = map Arrows (OP (P.length :: String -> Int) :×: P.length) parity
       in P.map (runArrows changed) ["", "a", "ab", "abc"] P.== [4, 3, 4, 3]
    ),
    ( "Procompose functor composition respects both variances",
      let combined = runArrows (map Arrows (secondStep ∘ firstStep) numeric)
          separate = runArrows (map Arrows secondStep (map Arrows firstStep numeric))
          expected n = 2 P.* ((3 P.* n P.- 2) P.^ (2 :: Int)) P.+ 9
       in sameOn ints combined separate P.&& sameOn ints combined expected
    ),
    ( "Procompose supports lmap and rmap",
      let left = lmap Arrows (P.length :: String -> Int) parity
          right = rmap Arrows P.length parity
       in runArrows left "abc" P.== "odd" P.&& runArrows right 2 P.== 4
    ),
    ( "Procompose supports dimap",
      let changed = dimap Arrows (P.length :: String -> Int) ("is " P.++) parity
       in P.map (runArrows changed) ["a", "ab"] P.== ["is odd", "is even"]
    ),
    ( "Nested Procompose maps its external endpoints",
      let changed = map Nested (OP (P.length :: String -> Int) :×: P.length) nested
       in P.map (runNested changed) ["a", "ab"] P.== [11, 12]
    )
  ]

-- All three categories have different kinds of object names. The source and
-- middle categories restrict their objects and have noncommuting arrows.
data Source :: CATEGORY Bool where
  Source :: (Int -> Int) -> Source 'True 'True

type instance Obj Source x = x ~ 'True

instance Semigroupoid Source where
  Source f ∘ Source g = Source (f ∘ g)

instance Category Source where
  identity _ = Source (identity _)

data Middle :: CATEGORY () where
  Middle :: (Int -> Int) -> Middle '() '()

type instance Obj Middle x = x ~ '()

instance Semigroupoid Middle where
  Middle f ∘ Middle g = Middle (f ∘ g)

instance Category Middle where
  identity _ = Middle (identity _)

type data IntoTypes :: PROFUNCTOR Middle Types

type instance Act IntoTypes ij = Int -> Snd ij

instance Functor IntoTypes where
  map _ (OP (Middle l) :×: r) f = r ∘ f ∘ l

type data Bridge :: PROFUNCTOR Source Middle

-- This Act family forgets both indices, exercising the need to specify the
-- existential middle object explicitly when mapping the component functors.
type instance Act Bridge ij = Int -> Int

instance Functor Bridge where
  map _ (OP (Source l) :×: Middle r) f = r ∘ f ∘ l

type Mixed = Procompose IntoTypes Bridge

mixed :: DataProcompose IntoTypes Bridge 'True Int
mixed = MkProcompose @'() (\n -> 5 P.* n P.+ 2) (\n -> n P.* n P.- 1)

-- Observe each stored component separately. Collapsing the composition alone
-- could hide an implementation that moved data across the intermediate object.
observeMixed :: DataProcompose IntoTypes Bridge i j -> Int -> (j, Int)
observeMixed (MkProcompose outer inner) n = (outer n, inner n)

mixedFirst, mixedSecond :: (Op Source × Types) '( 'True, Int) '( 'True, Int)
mixedFirst = OP (Source (P.+ 1)) :×: (P.* 2)
mixedSecond = OP (Source (P.* 3)) :×: (P.+ 5)

mixedChecks :: [(String, Bool)]
mixedChecks =
  [ ( "Procompose identity preserves both constrained components",
      sameOn
        ints
        (observeMixed (map Mixed (identity (type '( 'True, Int))) mixed))
        (observeMixed mixed)
    ),
    ( "Procompose maps constrained objects with different kinds",
      let changed = map Mixed (OP (Source (P.+ 3)) :×: (P.show ∘ (P.+ 9))) mixed
          expected n = (P.show (5 P.* n P.+ 11), (n P.+ 3) P.^ (2 :: Int) P.- 1)
       in sameOn ints (observeMixed changed) expected
    ),
    ( "Procompose composition preserves each stored component",
      let combined = observeMixed (map Mixed (mixedSecond ∘ mixedFirst) mixed)
          separate = observeMixed (map Mixed mixedSecond (map Mixed mixedFirst mixed))
          expected n = (10 P.* n P.+ 9, (3 P.* n P.+ 1) P.^ (2 :: Int) P.- 1)
       in sameOn ints combined separate P.&& sameOn ints combined expected
    ),
    ( "Procompose profunctor operations retain constrained object evidence",
      let changed = dimap Mixed (Source (P.+ 3)) P.show mixed
          separate = rmap Mixed P.show (lmap Mixed (Source (P.+ 3)) mixed)
          expected n = (P.show (5 P.* n P.+ 2), (n P.+ 3) P.^ (2 :: Int) P.- 1)
       in sameOn ints (observeMixed changed) expected
            P.&& sameOn ints (observeMixed separate) expected
    )
  ]

checks :: [(String, Bool)]
checks = arrowChecks P.++ mixedChecks
