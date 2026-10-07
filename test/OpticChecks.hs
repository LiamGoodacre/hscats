module OpticChecks (checks) where

import Cats
import Data.Kind (Type)
import Data.Type.Equality (type (~))
import Prelude (Bool (..), Char, Int, String)
import Prelude qualified as P

runLens :: LensLike '(a, b) '(s, t) -> (a -> b) -> s -> t
runLens optic = map (DataLens (Hom Types)) optic

runPrism :: PrismLike '(a, b) '(s, t) -> (a -> b) -> s -> t
runPrism optic = map (DataPrism (Hom Types)) optic

runGrate :: GrateLike '(a, b) '(s, t) -> (a -> b) -> s -> t
runGrate optic = map (DataGrate (Hom Types)) optic

runIso :: IsoLike '(a, b) '(s, t) -> (a -> b) -> s -> t
runIso optic = map (DataIso (Hom Types)) optic

getView :: ViewLike '(a, b) '(s, t) -> s -> a
getView (Window (Viewer get)) = get

getReview :: ReviewLike '(a, b) '(s, t) -> b -> t
getReview (Mirror (Viewer build)) = build

-- Representable interpretations exercise the public constructors as well as
-- composition. These signatures also check type-changing endpoints.
secondLens :: forall e a b. LensLike '(a, b) '((e, a), (e, b))
secondLens = lens @(HomFrom LensLike '(a, b)) P.id P.id (identity (type '(a, b)))

rightPrism :: forall e a b. PrismLike '(a, b) '(P.Either e a, P.Either e b)
rightPrism = prism @(HomFrom PrismLike '(a, b)) P.id P.id (identity (type '(a, b)))

pairGrate :: forall a b. GrateLike '(a, b) '((a, a), (b, b))
pairGrate =
  grate @(HomFrom GrateLike '(a, b))
    (\(x, y) flag -> if flag then y else x)
    (\values -> (values False, values True))
    (identity (type '(a, b)))

unitIso :: forall a b. IsoLike '(a, b) '((a, ()), (b, ()))
unitIso = iso @(HomFrom IsoLike '(a, b)) P.fst (\b -> (b, ())) (identity (type '(a, b)))

-- A rank-polymorphic alias must work for function and view interpretations.
polymorphicLens :: Lens Int String (Bool, Int) (Bool, String)
polymorphicLens @_ @p = lens @p @Int @String @(Bool, Int) @(Bool, String) @Bool P.id P.id

type LensInner = '(Int, String)

type LensMiddle = '((Bool, Int), (Bool, String))

type LensOuter = '((Char, (Bool, Int)), (Char, (Bool, String)))

type LensWhole = '((String, (Char, (Bool, Int))), (String, (Char, (Bool, String))))

lensInner :: LensLike LensInner LensMiddle
lensInner = secondLens

lensOuter :: LensLike LensMiddle LensOuter
lensOuter = secondLens

lensWhole :: LensLike LensOuter LensWhole
lensWhole = secondLens

type PrismMiddle = '(P.Either Bool Int, P.Either Bool String)

type PrismOuter = '(P.Either Char (P.Either Bool Int), P.Either Char (P.Either Bool String))

type PrismWhole = '(P.Either String (P.Either Char (P.Either Bool Int)), P.Either String (P.Either Char (P.Either Bool String)))

prismInner :: PrismLike LensInner PrismMiddle
prismInner = rightPrism

prismOuter :: PrismLike PrismMiddle PrismOuter
prismOuter = rightPrism

prismWhole :: PrismLike PrismOuter PrismWhole
prismWhole = rightPrism

type GrateMiddle = '((Int, Int), (String, String))

type GrateOuter = '(((Int, Int), (Int, Int)), ((String, String), (String, String)))

type GrateWhole = '((((Int, Int), (Int, Int)), ((Int, Int), (Int, Int))), (((String, String), (String, String)), ((String, String), (String, String))))

grateInner :: GrateLike LensInner GrateMiddle
grateInner = pairGrate

grateOuter :: GrateLike GrateMiddle GrateOuter
grateOuter = pairGrate

grateWhole :: GrateLike GrateOuter GrateWhole
grateWhole = pairGrate

prismSamples :: [P.Either Char (P.Either Bool Int)]
prismSamples = [P.Left 'x', P.Right (P.Left False), P.Right (P.Left True), P.Right (P.Right 7)]

deepPrismSamples :: [P.Either String (P.Either Char (P.Either Bool Int))]
deepPrismSamples = P.Left "skip" : P.map P.Right prismSamples

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs l r = P.all (\x -> l x P.== r x) xs

-- MkTensored must retain object evidence for its existential residual even
-- when that evidence is not recoverable from the tensor's object action.
data OnlyInt :: CATEGORY Type where
  OnlyInt :: (Int -> Int) -> OnlyInt Int Int

type instance Obj OnlyInt a = a ~ Int

instance Semigroupoid OnlyInt where
  OnlyInt f ∘ OnlyInt g = OnlyInt (f ∘ g)

instance Category OnlyInt where
  identity _ = OnlyInt P.id

type data ForgetResidual :: (OnlyInt × Types) --> Types

type instance Act ForgetResidual pair = Snd pair

residualEvidence :: Tensored ForgetResidual (Like Types) '(Int, Int) '(Int, Int) -> Int
residualEvidence (MkTensored @e _) = case (identity e :: OnlyInt e e) of
  OnlyInt f -> f 17

checks :: [(String, Bool)]
checks =
  [ ( "Lens constructor interprets a type-changing function",
      lens @(Hom Types) P.id P.id P.show (True, 7 :: Int) P.== (True, "7")
    ),
    ( "Lens constructor interprets a view",
      getView (lens @(HomFrom ViewLike LensInner) P.id P.id (identity LensInner)) (True, 7) P.== 7
    ),
    ( "Polymorphic Lens supports Hom and ViewLike domains",
      polymorphicLens @(Op Types × Types) @(Hom Types) P.show (True, 7) P.== (True, "7")
        P.&& getView (polymorphicLens @ViewLike @(HomFrom ViewLike LensInner) (identity LensInner)) (False, 8) P.== 8
    ),
    ( "Lens identity interprets directly",
      runLens (identity LensInner) P.show 7 P.== "7"
    ),
    ( "Lens composition preserves both residuals",
      runLens (lensOuter ∘ lensInner) P.show ('x', (True, 7)) P.== ('x', (True, "7"))
    ),
    ( "Lens interpretation preserves composition",
      sameOn
        [('x', (True, 7)), ('y', (False, -2))]
        (runLens (lensOuter ∘ lensInner) P.show)
        (runLens lensOuter (runLens lensInner P.show))
    ),
    ( "Lens left and right category identities",
      runLens (identity LensMiddle ∘ lensInner) P.show (False, 7) P.== (False, "7")
        P.&& runLens (lensInner ∘ identity LensInner) P.show (True, 8) P.== (True, "8")
    ),
    ( "Lens category associativity",
      let sample = ("keep", ('x', (True, 7)))
          expected = ("keep", ('x', (True, "7")))
       in runLens ((lensWhole ∘ lensOuter) ∘ lensInner) P.show sample P.== expected
            P.&& runLens (lensWhole ∘ (lensOuter ∘ lensInner)) P.show sample P.== expected
    ),
    ( "Lens view interpretation preserves composition",
      getView (map (DataLens (HomFrom ViewLike LensInner)) (lensOuter ∘ lensInner) (identity LensInner)) ('x', (True, 7))
        P.== getView
          ( map
              (DataLens (HomFrom ViewLike LensInner))
              lensOuter
              (map (DataLens (HomFrom ViewLike LensInner)) lensInner (identity LensInner))
          )
          ('x', (True, 7))
    ),
    ( "Lens interpretations respect residual reparameterization",
      let expanded =
            lens @(HomFrom LensLike LensInner)
              (\(flag, a) -> ((flag, flag), a))
              (\((flag, _), b) -> (flag, b))
              (identity LensInner)
          view optic = getView (map (DataLens (HomFrom ViewLike LensInner)) optic (identity LensInner))
       in sameOn [(True, 7), (False, -2)] (runLens expanded P.show) (runLens lensInner P.show)
            P.&& sameOn [(True, 7), (False, -2)] (view expanded) (view lensInner)
    ),
    ( "Prism constructor interprets both branches",
      let p = prism @(Hom Types) P.id P.id P.show :: P.Either Bool Int -> P.Either Bool String
       in p (P.Left False) P.== P.Left False P.&& p (P.Right 7) P.== P.Right "7"
    ),
    ( "Prism constructor interprets a review",
      getReview (prism @(HomFrom ReviewLike LensInner) P.id P.id (identity LensInner)) "new"
        P.== (P.Right "new" :: P.Either Bool String)
    ),
    ( "Prism identity interprets directly",
      runPrism (identity LensInner) P.show 7 P.== "7"
    ),
    ( "Prism composition preserves all failure branches",
      P.map (runPrism (prismOuter ∘ prismInner) P.show) prismSamples
        P.== [P.Left 'x', P.Right (P.Left False), P.Right (P.Left True), P.Right (P.Right "7")]
    ),
    ( "Prism skips the focus function on failure",
      runPrism (prismOuter ∘ prismInner) (\_ -> P.error "unexpected focus") (P.Right (P.Left True))
        P.== P.Right (P.Left True)
    ),
    ( "Prism interpretation preserves composition",
      sameOn prismSamples (runPrism (prismOuter ∘ prismInner) P.show) (runPrism prismOuter (runPrism prismInner P.show))
    ),
    ( "Prism left and right category identities",
      sameOn prismSamples (runPrism (identity PrismOuter ∘ prismOuter ∘ prismInner) P.show) (runPrism (prismOuter ∘ prismInner) P.show)
        P.&& sameOn prismSamples (runPrism (prismOuter ∘ prismInner ∘ identity LensInner) P.show) (runPrism (prismOuter ∘ prismInner) P.show)
    ),
    ( "Prism category associativity",
      sameOn
        deepPrismSamples
        (runPrism ((prismWhole ∘ prismOuter) ∘ prismInner) P.show)
        (runPrism (prismWhole ∘ (prismOuter ∘ prismInner)) P.show)
    ),
    ( "Prism review interpretation preserves composition",
      getReview (map (DataPrism (HomFrom ReviewLike LensInner)) (prismOuter ∘ prismInner) (identity LensInner)) "new"
        P.== getReview
          ( map
              (DataPrism (HomFrom ReviewLike LensInner))
              prismOuter
              (map (DataPrism (HomFrom ReviewLike LensInner)) prismInner (identity LensInner))
          )
          "new"
    ),
    ( "Prism interpretations respect residual reparameterization",
      let flipped =
            prism @(HomFrom PrismLike LensInner)
              (P.either (P.Left ∘ P.not) P.Right)
              (P.either (P.Left ∘ P.not) P.Right)
              (identity LensInner)
       in sameOn [P.Left False, P.Left True, P.Right 7] (runPrism flipped P.show) (runPrism prismInner P.show)
            P.&& getReview (map (DataPrism (HomFrom ReviewLike LensInner)) flipped (identity LensInner)) "new" P.== P.Right "new"
    ),
    ( "Grate constructor interprets a type-changing function",
      grate @(Hom Types)
        (\(x, y) flag -> if flag then y else x)
        (\values -> (values False, values True))
        P.show
        (3, 7 :: Int)
        P.== ("3", "7")
    ),
    ( "Grate identity interprets directly",
      runGrate (identity LensInner) P.show 7 P.== "7"
    ),
    ( "Grate composition preserves every position",
      runGrate (grateOuter ∘ grateInner) P.show ((1, 2), (3, 4)) P.== (("1", "2"), ("3", "4"))
    ),
    ( "Grate interpretation preserves composition",
      runGrate (grateOuter ∘ grateInner) P.show ((1, 2), (3, 4))
        P.== runGrate grateOuter (runGrate grateInner P.show) ((1, 2), (3, 4))
    ),
    ( "Grate left and right category identities",
      runGrate (identity GrateMiddle ∘ grateInner) P.show (1, 2) P.== ("1", "2")
        P.&& runGrate (grateInner ∘ identity LensInner) P.show (3, 4) P.== ("3", "4")
    ),
    ( "Grate category associativity",
      let sample = (((1, 2), (3, 4)), ((5, 6), (7, 8)))
          expected = ((("1", "2"), ("3", "4")), (("5", "6"), ("7", "8")))
       in runGrate ((grateWhole ∘ grateOuter) ∘ grateInner) P.show sample P.== expected
            P.&& runGrate (grateWhole ∘ (grateOuter ∘ grateInner)) P.show sample P.== expected
    ),
    ( "Grate zipping shares residual positions",
      zipWithGrate
        (grateOuter ∘ grateInner)
        (\x y -> P.show (10 P.* x P.+ y))
        ((1, 2), (3, 4))
        ((5, 6), (7, 8))
        P.== (("15", "26"), ("37", "48"))
    ),
    ( "Grate mapping and zipping respect residual reparameterization",
      let swapped =
            grate @(HomFrom GrateLike LensInner)
              (\(x, y) flag -> if flag then x else y)
              (\values -> (values True, values False))
              (identity LensInner)
          combine x y = P.show (10 P.* x P.+ y)
       in runGrate swapped P.show (1, 2) P.== runGrate grateInner P.show (1, 2)
            P.&& zipWithGrate swapped combine (1, 2) (3, 4) P.== zipWithGrate grateInner combine (1, 2) (3, 4)
    ),
    ( "Iso constructor and Hom interpretation",
      iso @(Hom Types) P.fst (\x -> (x, ())) P.show (7 :: Int, ()) P.== ("7", ())
    ),
    ( "Iso constructor and view interpretation",
      getView (iso @(HomFrom ViewLike LensInner) P.fst (\x -> (x, ())) (identity LensInner)) (7, ()) P.== 7
    ),
    ( "Iso constructor and review interpretation",
      getReview (iso @(HomFrom ReviewLike LensInner) P.fst (\x -> (x, ())) (identity LensInner)) "new" P.== ("new", ())
    ),
    ( "Iso identity and composition interpretations",
      runIso (identity LensInner) P.show 7 P.== "7"
        P.&& runIso (unitIso ∘ unitIso @Int @String) P.show ((7, ()), ()) P.== (("7", ()), ())
    ),
    ( "Iso view and review interpretations preserve composition",
      let outer = unitIso @(Int, ()) @(String, ())
          inner = unitIso @Int @String
          view optic = map (DataIso (HomFrom ViewLike LensInner)) optic
          review optic = map (DataIso (HomFrom ReviewLike LensInner)) optic
       in getView (view (outer ∘ inner) (identity LensInner)) ((7, ()), ())
            P.== getView (view outer (view inner (identity LensInner))) ((7, ()), ())
            P.&& getReview (review (outer ∘ inner) (identity LensInner)) "new"
              P.== getReview (review outer (review inner (identity LensInner))) "new"
    ),
    ( "Glass reversal round trips every represented shape",
      runLens (reversed (reversed lensInner)) P.show (True, 7) P.== (True, "7")
        P.&& runPrism (reversed (reversed prismInner)) P.show (P.Right 7) P.== P.Right "7"
        P.&& runGrate (reversed (reversed grateInner)) P.show (1, 2) P.== ("1", "2")
        P.&& runIso (reversed (reversed (unitIso @Int @String))) P.show (7, ()) P.== ("7", ())
    ),
    ( "Glass reversal reverses lens composition",
      runLens (reversed (reversed lensInner ∘ reversed lensOuter)) P.show ('x', (True, 7))
        P.== runLens (lensOuter ∘ lensInner) P.show ('x', (True, 7))
    ),
    ( "Glass reversal reverses prism composition",
      sameOn
        prismSamples
        (runPrism (reversed (reversed prismInner ∘ reversed prismOuter)) P.show)
        (runPrism (prismOuter ∘ prismInner) P.show)
    ),
    ( "Glass reversal reverses grate composition",
      runGrate (reversed (reversed grateInner ∘ reversed grateOuter)) P.show ((1, 2), (3, 4))
        P.== runGrate (grateOuter ∘ grateInner) P.show ((1, 2), (3, 4))
    ),
    ( "Glass LTR identities preserve a reversed lens",
      let backward = reversed lensInner
          left = identity (type '(String, Int)) ∘ backward
          right = backward ∘ identity (type '((Bool, String), (Bool, Int)))
       in runLens (reversed left) P.show (True, 7) P.== (True, "7")
            P.&& runLens (reversed right) P.show (False, 8) P.== (False, "8")
    ),
    ( "Like reversal swaps the two legs",
      case reversed (Like ((P.+ 1) :: Int -> Int) (P.show :: Int -> String)) of
        Like l r -> l 7 P.== "7" P.&& r 7 P.== 8
    ),
    ( "Tensored retains constrained residual object evidence",
      residualEvidence (MkTensored @Int (Like P.id P.id)) P.== 17
    )
  ]
