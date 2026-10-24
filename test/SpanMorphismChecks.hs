module SpanMorphismChecks (checks) where

import Cats
import Prelude (Bool (..), Int, Maybe (..), String)
import Prelude qualified as P

type SM = SpanMorphism Types Int Int Int Int Int Int

type CM = CospanMorphism Types Int Int Int Int Int Int

diagonal :: Span Types Int Int Int
diagonal = Span P.id P.id

codiagonal :: Cospan Types Int Int Int
codiagonal = Cospan P.id P.id

sm :: (Int -> Int) -> SM
sm f = SpanMorphism diagonal diagonal f f f

cm :: (Int -> Int) -> CM
cm f = CospanMorphism codiagonal codiagonal f f f

observeSM :: SM -> Int -> (Int, Int, Int)
observeSM (SpanMorphism _ _ h l r) n = (h n, l n, r n)

observeCM :: CM -> Int -> (Int, Int, Int)
observeCM (CospanMorphism _ _ h l r) n = (h n, l n, r n)

sameSM :: SM -> SM -> Bool
sameSM f g = P.all (\n -> observeSM f n P.== observeSM g n) [-3 .. 3]

sameCM :: CM -> CM -> Bool
sameCM f g = P.all (\n -> observeCM f n P.== observeCM g n) [-3 .. 3]

commutesSM :: (P.Eq c, P.Eq d) => [x] -> SpanMorphism Types x a b y c d -> Bool
commutesSM xs (SpanMorphism s t h l r) =
  P.all (\x -> spanLeft t (h x) P.== l (spanLeft s x) P.&& spanRight t (h x) P.== r (spanRight s x)) xs

commutesCM :: (P.Eq y) => [a] -> [b] -> CospanMorphism Types x a b y c d -> Bool
commutesCM as bs (CospanMorphism s t h l r) =
  P.all (\a -> h (cospanLeft s a) P.== cospanLeft t (l a)) as
    P.&& P.all (\b -> h (cospanRight s b) P.== cospanRight t (r b)) bs

injectSpan :: SpanMorphism Types Int Int Bool (Maybe Int) (Maybe Int) (Maybe Bool)
injectSpan =
  let s = Span (P.+ 1) P.even
   in SpanMorphism s (mapSpan (type (TypeConstructor Maybe)) s) Just Just Just

injectCospan :: CospanMorphism Types Int Int Bool (Maybe Int) (Maybe Int) (Maybe Bool)
injectCospan =
  let s = Cospan (P.+ 1) P.fromEnum
   in CospanMorphism s (mapCospan (type (TypeConstructor Maybe)) s) Just Just Just

checks :: [(String, Bool)]
checks =
  [ ("Span morphism squares with changed object types", commutesSM [-3 .. 3] injectSpan),
    ("Cospan morphism squares with changed object types", commutesCM [-3 .. 3] [False, True] injectCospan),
    ("Span morphism identity squares", commutesSM [-3 .. 3] (identitySpanMorphism diagonal)),
    ("Cospan morphism identity squares", commutesCM [-3 .. 3] [-3 .. 3] (identityCospanMorphism codiagonal)),
    ( "Span morphism composition order and squares",
      let f = composeSpanMorphisms (sm (P.* 3)) (sm (P.+ 1))
       in commutesSM [-3 .. 3] f P.&& observeSM f 7 P.== (24, 24, 24)
    ),
    ( "Cospan morphism composition order and squares",
      let f = composeCospanMorphisms (cm (P.* 3)) (cm (P.+ 1))
       in commutesCM [-3 .. 3] [-3 .. 3] f P.&& observeCM f 7 P.== (24, 24, 24)
    ),
    ( "Span morphism left and right identity",
      let f = sm (P.+ 1); i = identitySpanMorphism diagonal
       in sameSM (composeSpanMorphisms i f) f P.&& sameSM (composeSpanMorphisms f i) f
    ),
    ( "Cospan morphism left and right identity",
      let f = cm (P.+ 1); i = identityCospanMorphism codiagonal
       in sameCM (composeCospanMorphisms i f) f P.&& sameCM (composeCospanMorphisms f i) f
    ),
    ( "Span morphism associativity",
      let f = sm (P.+ 1); g = sm (P.* 3); h = sm P.negate
       in sameSM (composeSpanMorphisms h (composeSpanMorphisms g f)) (composeSpanMorphisms (composeSpanMorphisms h g) f)
    ),
    ( "Cospan morphism associativity",
      let f = cm (P.+ 1); g = cm (P.* 3); h = cm P.negate
       in sameCM (composeCospanMorphisms h (composeCospanMorphisms g f)) (composeCospanMorphisms (composeCospanMorphisms h g) f)
    ),
    ( "Mapping span morphisms preserves commuting squares",
      commutesSM [[], [1, 2], [-3]] (mapSpanMorphism (type (TypeConstructor [])) injectSpan)
    ),
    ( "Mapping cospan morphisms preserves commuting squares",
      commutesCM [[], [1, 2]] [[], [False, True]] (mapCospanMorphism (type (TypeConstructor [])) injectCospan)
    ),
    ( "Span morphism functor mapping preserves composition",
      let f = sm (P.+ 1)
          g = sm (P.* 3)
          l = mapSpanMorphism (type (TypeConstructor [])) (composeSpanMorphisms g f)
          r = composeSpanMorphisms (mapSpanMorphism (type (TypeConstructor [])) g) (mapSpanMorphism (type (TypeConstructor [])) f)
       in P.all (\xs -> spanApexMap l xs P.== spanApexMap r xs P.&& spanLeftMap l xs P.== spanLeftMap r xs P.&& spanRightMap l xs P.== spanRightMap r xs) [[], [1, 2]]
    ),
    ( "Cospan morphism functor mapping preserves composition",
      let f = cm (P.+ 1)
          g = cm (P.* 3)
          l = mapCospanMorphism (type (TypeConstructor [])) (composeCospanMorphisms g f)
          r = composeCospanMorphisms (mapCospanMorphism (type (TypeConstructor [])) g) (mapCospanMorphism (type (TypeConstructor [])) f)
       in P.all (\xs -> cospanApexMap l xs P.== cospanApexMap r xs P.&& cospanLeftMap l xs P.== cospanLeftMap r xs P.&& cospanRightMap l xs P.== cospanRightMap r xs) [[], [1, 2]]
    ),
    ("Span morphism dual round trip", sameSM (sm (P.+ 1)) (unOpSpanMorphism (opSpanMorphism (sm (P.+ 1))))),
    ("Cospan morphism dual round trip", sameCM (cm (P.+ 1)) (unOpCospanMorphism (opCospanMorphism (cm (P.+ 1))))),
    ( "Duality reverses span morphism composition",
      let f = sm (P.+ 1); g = sm (P.* 3)
       in sameSM (composeSpanMorphisms g f) (unOpSpanMorphism (composeCospanMorphisms (opSpanMorphism f) (opSpanMorphism g)))
    ),
    ( "Duality reverses cospan morphism composition",
      let f = cm (P.+ 1); g = cm (P.* 3)
       in sameCM (composeCospanMorphisms g f) (unOpCospanMorphism (composeSpanMorphisms (opCospanMorphism f) (opCospanMorphism g)))
    )
  ]
