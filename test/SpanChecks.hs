module SpanChecks (checks) where

import Cats
import Data.Type.Equality ((:~:) (Refl))
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

sampleSpan :: Span Types Int Int Bool
sampleSpan = Span (P.+ 1) P.even

sampleCospan :: Cospan Types Int Int Bool
sampleCospan = Cospan (P.+ 1) (\b -> if b then 10 else 20)

spanAt :: Span Types x a b -> x -> (a, b)
spanAt (Span l r) x = (l x, r x)

cospanAt :: Cospan Types x a b -> a -> b -> (x, x)
cospanAt (Cospan l r) a b = (l a, r b)

sameSpan :: (P.Eq a, P.Eq b) => Span Types Int a b -> Span Types Int a b -> Bool
sameSpan l r = P.all (\x -> spanAt l x P.== spanAt r x) [-3 .. 3]

sameCospan :: (P.Eq x) => Cospan Types x Int Bool -> Cospan Types x Int Bool -> Bool
sameCospan l r =
  P.and [cospanAt l a b P.== cospanAt r a b | a <- [-3 .. 3], b <- [False, True]]

type SpanIndex = '(Int, '(Int, Bool))

spanStep1, spanStep2 :: DomainOf (Spans Types) SpanIndex SpanIndex
spanStep1 = OP (P.+ 2) :×: ((P.* 3) :×: P.not)
spanStep2 = OP (P.* 5) :×: ((P.+ 7) :×: P.not)

cospanStep1, cospanStep2 :: DomainOf (Cospans Types) SpanIndex SpanIndex
cospanStep1 = (P.+ 2) :×: (OP (P.* 3) :×: OP P.not)
cospanStep2 = (P.* 5) :×: (OP (P.+ 7) :×: OP P.not)

-- These signatures also check that the views work for arbitrary object
-- constraints, rather than just the unconstrained objects of Types.
reindexSpan ::
  forall k x y a b.
  (Category k, x ∈ k, y ∈ k, a ∈ k, b ∈ k) =>
  k y x -> Span k x a b -> Span k y a b
reindexSpan f = map (SpansBetween k a b) (OP f)

reindexCospan ::
  forall k x y a b.
  (Category k, x ∈ k, y ∈ k, a ∈ k, b ∈ k) =>
  k x y -> Cospan k x a b -> Cospan k y a b
reindexCospan f = map (CospansBetween k a b) f

-- A category whose objects have kind Bool exercises kind polymorphism.
boolSpan :: Span (:~:) 'True 'True 'True
boolSpan = reindexSpan Refl (mapSpan Id (Span Refl Refl))

boolCospan :: Cospan (:~:) 'False 'False 'False
boolCospan = reindexCospan Refl (mapCospan Id (Cospan Refl Refl))

checks :: [(String, Bool)]
checks =
  [ ( "Span product encoding",
      spanToProduct (∧) sampleSpan 2 P.== (3, True)
    ),
    ( "Cospan coproduct encoding",
      P.map (cospanToCoproduct (∨) sampleCospan) [P.Left 2, P.Right True, P.Right False]
        P.== [3, 10, 20]
    ),
    ( "Span product round trip",
      sameSpan sampleSpan (spanFromProduct (∧) (spanToProduct (∧) sampleSpan))
    ),
    ( "Cospan coproduct round trip",
      sameCospan sampleCospan (cospanFromCoproduct (∨) (cospanToCoproduct (∨) sampleCospan))
    ),
    ( "Product arrow round trip",
      let f (n :: Int) = (n P.* 2, P.odd n)
       in P.all (\n -> spanToProduct (∧) (spanFromProduct (∧) f) n P.== f n) [-3 .. 3]
    ),
    ( "Coproduct arrow round trip",
      let f = P.either (P.* 2) (\b -> if b then 1 else 0) :: P.Either Int Bool -> Int
       in P.all
            (\v -> cospanToCoproduct (∨) (cospanFromCoproduct (∨) f) v P.== f v)
            [P.Left (-2), P.Left 3, P.Right False, P.Right True]
    ),
    ( "Span product category round trip",
      sameSpan sampleSpan (spanFromArrow (spanToArrow sampleSpan))
    ),
    ( "Cospan product category round trip",
      sameCospan sampleCospan (cospanFromArrow (cospanToArrow sampleCospan))
    ),
    ("Span dual round trip", sameSpan sampleSpan (unOpSpan (opSpan sampleSpan))),
    ("Cospan dual round trip", sameCospan sampleCospan (unOpCospan (opCospan sampleCospan))),
    ("Span swap", spanAt (swapSpan sampleSpan) 2 P.== (True, 3)),
    ("Cospan swap", cospanAt (swapCospan sampleCospan) True 2 P.== (10, 3)),
    ( "Spans identity law",
      sameSpan sampleSpan (map (Spans Types) (identity SpanIndex) sampleSpan)
    ),
    ( "Spans composition law",
      sameSpan
        (map (Spans Types) (spanStep2 ∘ spanStep1) sampleSpan)
        (map (Spans Types) spanStep2 (map (Spans Types) spanStep1 sampleSpan))
    ),
    ( "Cospans identity law",
      sameCospan sampleCospan (map (Cospans Types) (identity SpanIndex) sampleCospan)
    ),
    ( "Cospans composition law",
      sameCospan
        (map (Cospans Types) (cospanStep2 ∘ cospanStep1) sampleCospan)
        (map (Cospans Types) cospanStep2 (map (Cospans Types) cospanStep1 sampleCospan))
    ),
    ( "Span fixed apex",
      spanAt (map (SpansFrom Types Int) ((P.show :: Int -> String) :×: P.not) sampleSpan) 2
        P.== ("3", False)
    ),
    ( "Cospan fixed apex",
      cospanAt (map (CospansTo Types Int) (OP (P.length :: String -> Int) :×: OP P.not) sampleCospan) "ab" True
        P.== (3, 20)
    ),
    ( "Span fixed endpoints",
      spanAt (reindexSpan (P.length :: [Int] -> Int) sampleSpan) [4, 5] P.== (3, True)
    ),
    ( "Cospan fixed endpoints",
      cospanAt (reindexCospan (P.show :: Int -> String) sampleCospan) 2 True P.== ("3", "10")
    ),
    ( "Span curried natural transformation",
      sameSpan
        ((map (Curry₁ (Spans Types)) (OP ((P.+ 2) :: Int -> Int)) $$ (Int, Bool)) sampleSpan)
        (reindexSpan (P.+ 2) sampleSpan)
    ),
    ( "Cospan curried natural transformation",
      sameCospan
        ((map (Curry₁ (Cospans Types)) ((P.+ 2) :: Int -> Int) $$ (Int, Bool)) sampleCospan)
        (reindexCospan (P.+ 2) sampleCospan)
    ),
    ( "Map whole span",
      spanAt (mapSpan (type (Constructor [])) sampleSpan) [1, 2] P.== ([2, 3], [False, True])
    ),
    ( "Map whole cospan",
      cospanAt (mapCospan (type (Constructor [])) sampleCospan) [1, 2] [True, False] P.== ([2, 3], [10, 20])
    ),
    ("Span with Bool objects", case boolSpan of Span Refl Refl -> True),
    ("Cospan with Bool objects", case boolCospan of Cospan Refl Refl -> True)
  ]
