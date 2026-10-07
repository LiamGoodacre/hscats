module MonoidalChecks (checks) where

import Cats
import DayChecks qualified as Day
import Prelude (Bool (..), Char, Int, String)
import Prelude qualified as P

type Tensor p a b = Act p '(a, b)

-- Return the two paths around each naturality square. Keeping these helpers
-- category-polymorphic also tests propagation of the object constraints.
rightNaturality ::
  forall {k} (p :: BINARY_OP k) a b c a' b' c'.
  (Associative p, a ∈ k, b ∈ k, c ∈ k, a' ∈ k, b' ∈ k, c' ∈ k) =>
  k a a' -> k b b' -> k c c' ->
  ( k (Tensor p (Tensor p a b) c) (Tensor p a' (Tensor p b' c')),
    k (Tensor p (Tensor p a b) c) (Tensor p a' (Tensor p b' c'))
  )
rightNaturality f g h =
  ( rassoc p a' b' c' ∘ map p (map p (f :×: g) :×: h),
    map p (f :×: map p (g :×: h)) ∘ rassoc p a b c
  )

leftNaturality ::
  forall {k} (p :: BINARY_OP k) a b c a' b' c'.
  (Associative p, a ∈ k, b ∈ k, c ∈ k, a' ∈ k, b' ∈ k, c' ∈ k) =>
  k a a' -> k b b' -> k c c' ->
  ( k (Tensor p a (Tensor p b c)) (Tensor p (Tensor p a' b') c'),
    k (Tensor p a (Tensor p b c)) (Tensor p (Tensor p a' b') c')
  )
leftNaturality f g h =
  ( lassoc p a' b' c' ∘ map p (f :×: map p (g :×: h)),
    map p (map p (f :×: g) :×: h) ∘ lassoc p a b c
  )

leftUnitNaturality ::
  forall {k} (p :: BINARY_OP k) a b.
  (Monoidal p, a ∈ k, b ∈ k) =>
  k a b ->
  (k (Tensor p (MonoidalEmpty p) a) b, k (Tensor p (MonoidalEmpty p) a) b)
leftUnitNaturality h =
  (h ∘ idl @_ @p @a, idl @_ @p @b ∘ map p (identity (MonoidalEmpty p) :×: h))

rightUnitNaturality ::
  forall {k} (p :: BINARY_OP k) a b.
  (Monoidal p, a ∈ k, b ∈ k) =>
  k a b ->
  (k (Tensor p a (MonoidalEmpty p)) b, k (Tensor p a (MonoidalEmpty p)) b)
rightUnitNaturality h =
  (h ∘ idr @_ @p @a, idr @_ @p @b ∘ map p (h :×: identity (MonoidalEmpty p)))

sameOn :: (P.Eq b) => [a] -> (a -> b, a -> b) -> Bool
sameOn xs (l, r) = P.all (\x -> l x P.== r x) xs

ints :: [Int]
ints = [-3 .. 3]

productLeft :: [((Int, Bool), Char)]
productLeft = [((n, b), c) | n <- ints, b <- [False, True], c <- ['x', 'y']]

productRight :: [(Int, (Bool, Char))]
productRight = [(n, (b, c)) | ((n, b), c) <- productLeft]

sumLeft :: [P.Either (P.Either Int Bool) Char]
sumLeft = P.map (P.Left ∘ P.Left) ints P.++ [P.Left (P.Right False), P.Left (P.Right True), P.Right 'x', P.Right 'y']

sumRight :: [P.Either Int (P.Either Bool Char)]
sumRight = P.map P.Left ints P.++ [P.Right (P.Left False), P.Right (P.Left True), P.Right (P.Right 'x'), P.Right (P.Right 'y')]

type List = Constructor []
type ProductDay = Day₁ @Types @Types (∧)
type SumDay = Day₁ @Types @Types (∨)

reverseList, firstTwo, dropFirst :: List ~> List
reverseList = EXP \_ -> P.reverse
firstTwo = EXP \_ -> P.take 2
dropFirst = EXP \_ -> P.drop 1

checks :: [(String, Bool)]
checks =
  [ ( "Product right associator naturality changes object types",
      sameOn productLeft (rightNaturality @(∧) P.show P.fromEnum (P.== 'x'))
    ),
    ( "Product left associator naturality changes object types",
      sameOn productRight (leftNaturality @(∧) P.show P.fromEnum (P.== 'x'))
    ),
    ( "Coproduct right associator naturality covers all branches",
      sameOn sumLeft (rightNaturality @(∨) P.show P.fromEnum (P.== 'x'))
    ),
    ( "Coproduct left associator naturality covers all branches",
      sameOn sumRight (leftNaturality @(∨) P.show P.fromEnum (P.== 'x'))
    ),
    ( "Product left unitor naturality",
      sameOn [((), n) | n <- ints] (leftUnitNaturality @(∧) P.show)
    ),
    ( "Product right unitor naturality",
      sameOn [(n, ()) | n <- ints] (rightUnitNaturality @(∧) P.show)
    ),
    ( "Coproduct left unitor naturality",
      sameOn (P.map P.Right ints) (leftUnitNaturality @(∨) P.show)
    ),
    ( "Coproduct right unitor naturality",
      sameOn (P.map P.Left ints) (rightUnitNaturality @(∨) P.show)
    ),
    ( "Day product right associator naturality",
      let (l, r) = rightNaturality @ProductDay reverseList firstTwo dropFirst
       in Day.productRightValues ((l $$ Int) Day.productLeft) P.== Day.productRightValues ((r $$ Int) Day.productLeft)
    ),
    ( "Day product left associator naturality",
      let (l, r) = leftNaturality @ProductDay reverseList firstTwo dropFirst
       in Day.productLeftValues ((l $$ Int) Day.productRight) P.== Day.productLeftValues ((r $$ Int) Day.productRight)
    ),
    ( "Day coproduct right associator naturality",
      let (l, r) = rightNaturality @SumDay reverseList firstTwo dropFirst
       in Day.sumRightValues ((l $$ Int) Day.sumLeft) P.== Day.sumRightValues ((r $$ Int) Day.sumLeft)
    ),
    ( "Day coproduct left associator naturality",
      let (l, r) = leftNaturality @SumDay reverseList firstTwo dropFirst
       in Day.sumLeftValues ((l $$ Int) Day.sumRight) P.== Day.sumLeftValues ((r $$ Int) Day.sumRight)
    ),
    ( "Day product left unitor naturality",
      let (l, r) = leftUnitNaturality @ProductDay reverseList
       in (l $$ Int) Day.productUnitLeft P.== (r $$ Int) Day.productUnitLeft
    ),
    ( "Day product right unitor naturality",
      let (l, r) = rightUnitNaturality @ProductDay reverseList
       in (l $$ Int) Day.productUnitRight P.== (r $$ Int) Day.productUnitRight
    ),
    ( "Day coproduct left unitor naturality",
      let (l, r) = leftUnitNaturality @SumDay reverseList
       in (l $$ Int) Day.sumUnitLeft P.== (r $$ Int) Day.sumUnitLeft
    ),
    ( "Day coproduct right unitor naturality",
      let (l, r) = rightUnitNaturality @SumDay reverseList
       in (l $$ Int) Day.sumUnitRight P.== (r $$ Int) Day.sumUnitRight
    )
  ]
