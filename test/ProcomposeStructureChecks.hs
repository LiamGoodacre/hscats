module ProcomposeStructureChecks (checks) where

import Cats
import DayChecks (Add (..))
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type H = Hom Add

type Tensor = Procompose₁ @Add

type Twice = Procompose H H

type RightThree = Procompose H Twice

type LeftThree = Procompose Twice H

type FourLeft = Procompose LeftThree H

type FourRight = Procompose H RightThree

shift :: Int -> H ~> H
shift n = EXP \_ (Add m) -> Add (m P.+ n)

pair :: DataProcompose H H '() '()
pair = MkProcompose @'() (Add 2) (Add 3)

inspectPair :: DataProcompose H H i j -> (Int, Int)
inspectPair (MkProcompose (Add l) (Add r)) = (l, r)

leftThree :: Act LeftThree '( '(), '())
leftThree = MkProcompose @'() pair (Add 5)

rightThree :: Act RightThree '( '(), '())
rightThree = MkProcompose @'() (Add 2) (MkProcompose @'() (Add 3) (Add 5))

inspectLeft :: Act LeftThree '( '(), '()) -> (Int, Int, Int)
inspectLeft (MkProcompose (MkProcompose (Add a) (Add b)) (Add c)) = (a, b, c)

inspectRight :: Act RightThree '( '(), '()) -> (Int, Int, Int)
inspectRight (MkProcompose (Add a) (MkProcompose (Add b) (Add c))) = (a, b, c)

fourLeft :: Act FourLeft '( '(), '())
fourLeft = MkProcompose @'() leftThree (Add 7)

inspectFour :: Act FourRight '( '(), '()) -> (Int, Int, Int, Int)
inspectFour (MkProcompose (Add a) (MkProcompose (Add b) (MkProcompose (Add c) (Add d)))) = (a, b, c, d)

pentagonShort, pentagonLong :: FourLeft ~> FourRight
pentagonShort = rassoc Tensor H H Twice ∘ rassoc Tensor Twice H H
pentagonLong =
  map Tensor (identity H :×: rassoc Tensor H H H)
    ∘ rassoc Tensor H Twice H
    ∘ map Tensor (rassoc Tensor H H H :×: identity H)

-- The Types tensor is tested with a profunctor whose results branch, so unit
-- and coherence checks observe both order and multiplicity of outputs.
type data ListArrows :: PROFUNCTOR Types Types

type instance Act ListArrows ab = Fst ab -> [Snd ab]

instance Functor ListArrows where
  map _ (OP l :×: r) f = P.map r ∘ f ∘ l

type TypesTensor = Procompose₁ @Types

type Functions = Hom Types

singleton :: Functions ~> ListArrows
singleton = EXP \_ f -> \a -> [f a]

reverseOutputs :: ListArrows ~> ListArrows
reverseOutputs = EXP \_ f -> P.reverse ∘ f

leftUnit :: DataProcompose Functions ListArrows Int String
leftUnit = MkProcompose @Bool (\b -> if b then "yes" else "no") (\n -> [P.even n, n P.> 0])

rightUnit :: DataProcompose ListArrows Functions Int Int
rightUnit = MkProcompose @Bool (\b -> if b then [7, 3] else [9, 1]) P.even

runLeft :: DataProcompose Functions ListArrows a b -> a -> [b]
runLeft (MkProcompose f g) = P.map f ∘ g

runRight :: DataProcompose ListArrows Functions a b -> a -> [b]
runRight (MkProcompose f g) = f ∘ g

runLists :: DataProcompose ListArrows ListArrows a b -> a -> [b]
runLists (MkProcompose f g) = P.concatMap f ∘ g

triangleInput :: DataProcompose (Procompose ListArrows Functions) ListArrows Int String
triangleInput =
  MkProcompose @Bool
    (MkProcompose @Int (\n -> [P.show n, "x"]) (\b -> if b then 7 else 9))
    (\n -> [P.even n, False])

triangleDirect, triangleViaAssoc :: Procompose (Procompose ListArrows Functions) ListArrows ~> Procompose ListArrows ListArrows
triangleDirect = map TypesTensor (idr @_ @TypesTensor @ListArrows :×: identity ListArrows)
triangleViaAssoc =
  map TypesTensor (identity ListArrows :×: idl @_ @TypesTensor @ListArrows)
    ∘ rassoc TypesTensor ListArrows Functions ListArrows

ints :: [Int]
ints = [-3 .. 3]

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs f g = P.all (\x -> f x P.== g x) xs

checks :: [(String, Bool)]
checks =
  [ ( "Procompose maps both natural transformation components",
      inspectPair ((procomposeNat (shift 1) (shift 10) $$ ((), ())) pair) P.== (3, 13)
    ),
    ( "Procompose tensor preserves identity on each component",
      inspectPair ((map Tensor (identity H :×: identity H) $$ ((), ())) pair) P.== (2, 3)
    ),
    ( "Procompose tensor preserves composition on each component",
      let first = shift 1 :×: shift 10
          second = shift 3 :×: shift 20
          together = (map Tensor (second ∘ first) $$ ((), ())) pair
          separately = ((map Tensor second ∘ map Tensor first) $$ ((), ())) pair
       in inspectPair together P.== (6, 33) P.&& inspectPair separately P.== (6, 33)
    ),
    ( "Procompose horizontal transformation is natural in endpoints",
      let endpoints = OP (Add 7) :×: Add 11
          changed = procomposeNat (shift 1) (shift 10)
       in inspectPair ((changed $$ ((), ())) (map Twice endpoints pair))
            P.== inspectPair (map Twice endpoints ((changed $$ ((), ())) pair))
    ),
    ( "Procompose associators preserve each raw component",
      inspectLeft ((procomposeLassoc @H @H @H $$ ((), ())) rightThree) P.== (2, 3, 5)
        P.&& inspectRight ((procomposeRassoc @H @H @H $$ ((), ())) leftThree) P.== (2, 3, 5)
    ),
    ( "Procompose associators are inverse in both directions",
      inspectLeft (((lassoc Tensor H H H ∘ rassoc Tensor H H H) $$ ((), ())) leftThree) P.== (2, 3, 5)
        P.&& inspectRight (((rassoc Tensor H H H ∘ lassoc Tensor H H H) $$ ((), ())) rightThree) P.== (2, 3, 5)
    ),
    ( "Procompose associator is natural in profunctor arguments",
      let leftChanges = map Tensor (map Tensor (shift 1 :×: shift 10) :×: shift 100)
          rightChanges = map Tensor (shift 1 :×: map Tensor (shift 10 :×: shift 100))
          l = ((rassoc Tensor H H H ∘ leftChanges) $$ ((), ())) leftThree
          r = ((rightChanges ∘ rassoc Tensor H H H) $$ ((), ())) leftThree
       in inspectRight l P.== (3, 13, 105) P.&& inspectRight r P.== (3, 13, 105)
    ),
    ( "Procompose associator is natural in endpoints",
      let endpoints = OP (Add 7) :×: Add 11
          l = (procomposeRassoc @H @H @H $$ ((), ())) (map LeftThree endpoints leftThree)
          r = map RightThree endpoints ((procomposeRassoc @H @H @H $$ ((), ())) leftThree)
       in inspectRight l P.== (13, 3, 12) P.&& inspectRight r P.== (13, 3, 12)
    ),
    ( "Procompose pentagon preserves all raw components",
      inspectFour ((pentagonShort $$ ((), ())) fourLeft) P.== (2, 3, 5, 7)
        P.&& inspectFour ((pentagonLong $$ ((), ())) fourLeft) P.== (2, 3, 5, 7)
    ),
    ( "Generic left unit removal after insertion is identity",
      case ((procomposeIdl @H ∘ procomposeCoidl @H) $$ ((), ())) (Add 7) of
        Add n -> n P.== 7
    ),
    ( "Generic right unit removal after insertion is identity",
      case ((procomposeIdr @H ∘ procomposeCoidr @H) $$ ((), ())) (Add 7) of
        Add n -> n P.== 7
    ),
    ( "Generic left unit round trip changes the raw representative",
      inspectPair pair P.== (2, 3)
        P.&& inspectPair (((procomposeCoidl @H ∘ procomposeIdl @H) $$ ((), ())) pair) P.== (0, 5)
    ),
    ( "Generic right unit round trip changes the raw representative",
      inspectPair pair P.== (2, 3)
        P.&& inspectPair (((procomposeCoidr @H ∘ procomposeIdr @H) $$ ((), ())) pair) P.== (5, 0)
    ),
    ( "Types horizontal composition changes both profunctor tags",
      let arrows = MkProcompose @Bool (\b -> if b then "even" else "odd") P.even
          changed = (procomposeNat singleton singleton $$ (Int, String)) arrows
       in P.map (runLists changed) [0, 1] P.== [["even"], ["odd"]]
    ),
    ( "Types left unit maps output and retains branching order",
      P.map ((idl @_ @TypesTensor @ListArrows $$ (Int, String)) leftUnit) [-1, 0, 1]
        P.== [["no", "no"], ["yes", "no"], ["no", "yes"]]
    ),
    ( "Types right unit maps input and retains branching order",
      P.map ((idr @_ @TypesTensor @ListArrows $$ (Int, Int)) rightUnit) [0, 1]
        P.== [[7, 3], [9, 1]]
    ),
    ( "Types left unit insertion and removal",
      let f n = [n P.+ 1, 3 P.* n]
       in sameOn ints (((idl @_ @TypesTensor @ListArrows ∘ coidl @_ @TypesTensor @ListArrows) $$ (Int, Int)) f) f
    ),
    ( "Types right unit insertion and removal",
      let f n = [n P.+ 1, 3 P.* n]
       in sameOn ints (((idr @_ @TypesTensor @ListArrows ∘ coidr @_ @TypesTensor @ListArrows) $$ (Int, Int)) f) f
    ),
    ( "Types left unit reverse round trip is extensionally identity",
      sameOn ints (runLeft (((coidl @_ @TypesTensor @ListArrows ∘ idl @_ @TypesTensor @ListArrows) $$ (Int, String)) leftUnit)) (runLeft leftUnit)
    ),
    ( "Types right unit reverse round trip is extensionally identity",
      sameOn ints (runRight (((coidr @_ @TypesTensor @ListArrows ∘ idr @_ @TypesTensor @ListArrows) $$ (Int, Int)) rightUnit)) (runRight rightUnit)
    ),
    ( "Types left unitor is natural in the profunctor",
      let l = reverseOutputs ∘ idl @_ @TypesTensor @ListArrows
          r = idl @_ @TypesTensor @ListArrows ∘ map TypesTensor (identity Functions :×: reverseOutputs)
       in sameOn ints ((l $$ (Int, String)) leftUnit) ((r $$ (Int, String)) leftUnit)
    ),
    ( "Types right unitor is natural in the profunctor",
      let l = reverseOutputs ∘ idr @_ @TypesTensor @ListArrows
          r = idr @_ @TypesTensor @ListArrows ∘ map TypesTensor (reverseOutputs :×: identity Functions)
       in sameOn ints ((l $$ (Int, Int)) rightUnit) ((r $$ (Int, Int)) rightUnit)
    ),
    ( "Procompose triangle retains output order and multiplicity",
      let l = runLists ((triangleDirect $$ (Int, String)) triangleInput)
          r = runLists ((triangleViaAssoc $$ (Int, String)) triangleInput)
       in sameOn ints l r P.&& P.map l [0, 1] P.== [["7", "x", "9", "x"], ["9", "x", "9", "x"]]
    )
  ]
