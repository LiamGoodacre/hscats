module OppositeChecks (checks) where

import Cats
import Data.Type.Equality (type (~))
import Prelude (Bool (..), Char, Int, String)
import Prelude qualified as P

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs f g = P.all (\x -> f x P.== g x) xs

ints :: [Int]
ints = [-3 .. 3]

type List = Constructor []

reverseList, firstTwo :: List ~> List
reverseList = EXP \_ -> P.reverse
firstTwo = EXP \_ -> P.take 2

-- Non-Type object names, a nontrivial object constraint, and noncommuting
-- arrows ensure the construction does not depend on the special case Types.
data TrueOnly :: CATEGORY Bool where
  TrueOnly :: (Int -> Int) -> TrueOnly 'True 'True

type instance Obj TrueOnly x = x ~ 'True

instance Semigroupoid TrueOnly where
  TrueOnly f ∘ TrueOnly g = TrueOnly (f ∘ g)

instance Category TrueOnly where
  identity _ = TrueOnly (identity _)

type data ReadArrow :: TrueOnly --> Types

type instance Act ReadArrow x = Int

instance Functor ReadArrow where
  map _ (TrueOnly f) = f

functorChecks :: [(String, Bool)]
functorChecks =
  [ ( "Opposite functor identity",
      runOP (map (OpFunctor List) (identity Int)) [1, 2, 3] P.== [1, 2, 3]
    ),
    ( "Opposite functor composition reverses underlying arrows",
      let f = OP ((P.+ 1) :: Int -> Int)
          g = OP ((P.* 3) :: Int -> Int)
          combined = runOP (map (OpFunctor List) (g ∘ f))
          separate = runOP (map (OpFunctor List) g ∘ map (OpFunctor List) f)
       in combined [1, 2] P.== [4, 7] P.&& separate [1, 2] P.== [4, 7]
    ),
    ( "Opposite functor with constrained Bool objects and a Types codomain",
      let f = OP (TrueOnly (P.+ 1))
          g = OP (TrueOnly (P.* 3))
       in sameOn ints (runOP (map (OpFunctor ReadArrow) (g ∘ f))) (\n -> 3 P.* n P.+ 1)
            P.&& sameOn ints (runOP (map (OpFunctor ReadArrow) (identity (type 'True)))) (identity _)
    ),
    ( "Opposite natural transformation round trips",
      let dual = opNat reverseList
       in (unOpNat dual $$ Int) [1, 2, 3] P.== [3, 2, 1]
            P.&& runOP (opNat (unOpNat dual) $$ Int) [1, 2, 3] P.== [3, 2, 1]
    ),
    ( "Opposite natural transformation reverses composition",
      let combined = runOP (opNat (firstTwo ∘ reverseList) $$ Int)
          separate = runOP ((opNat reverseList ∘ opNat firstTwo) $$ Int)
       in combined [1, 2, 3, 4] P.== [4, 3] P.&& separate [1, 2, 3, 4] P.== [4, 3]
    ),
    ( "Double opposite arrow round trips",
      let f = (P.+ 7) :: Int -> Int
       in sameOn ints (unOpOp (opOp f)) f
            P.&& sameOn ints (unOpOp (opOp (unOpOp (OP (OP f))))) f
    ),
    ( "Double opposite functors are inverse",
      let f = P.show :: Int -> String
       in sameOn ints (map FromDoubleOp (map ToDoubleOp f)) f
            P.&& sameOn ints (unOpOp (map ToDoubleOp (map FromDoubleOp (opOp f)))) f
    ),
    ( "Double opposite functors preserve identity and composition",
      let f = (P.+ 1) :: Int -> Int
          g = (P.* 3) :: Int -> Int
       in sameOn ints (unOpOp (map ToDoubleOp (identity Int))) (identity _)
            P.&& sameOn ints (unOpOp (map ToDoubleOp (g ∘ f))) (unOpOp (map ToDoubleOp g ∘ map ToDoubleOp f))
            P.&& sameOn ints (map FromDoubleOp (identity Int)) (identity _)
            P.&& sameOn ints (map FromDoubleOp (opOp g ∘ opOp f)) (g ∘ f)
    ),
    ( "Double opposite functor acts like the original",
      unOpOp (map (OpFunctor (OpFunctor List)) (opOp (P.show :: Int -> String))) [1, 2]
        P.== ["1", "2"]
    ),
    ( "Double opposite conversions preserve constrained objects",
      case map FromDoubleOp (map ToDoubleOp (identity (type 'True) :: TrueOnly 'True 'True)) of
        TrueOnly f -> sameOn ints f (identity _)
    )
  ]

-- These signatures also check propagation of arbitrary object constraints.
leftTriangle ::
  forall {c} {d} (f :: c --> d) g a.
  (f ⊣ g, a ∈ c) =>
  d (Act f a) (Act f a)
leftTriangle = counit (type '(f, g)) (Act f a) ∘ map f (unit (type '(g, f)) a)

rightTriangle ::
  forall {c} {d} (f :: c --> d) g b.
  (f ⊣ g, b ∈ d) =>
  c (Act g b) (Act g b)
rightTriangle = map g (counit (type '(f, g)) b) ∘ unit (type '(g, f)) (Act g b)

type DualProduct = OpFunctor (∧)

type DualDiagonal = OpFunctor (Δ₂ Types)

type DualSum = OpFunctor (∨)

productLegs :: (Types × Types) '(Int, Int) '(Int, Bool)
productLegs = (P.+ 1) :×: P.even

dualProductArrow :: Op Types (Int, Bool) Int
dualProductArrow = rightToLeft DualDiagonal DualProduct (OP productLegs)

sumArrow :: P.Either Int Bool -> String
sumArrow = P.either P.show (\b -> if b then "yes" else "no")

sumInputs :: [P.Either Int Bool]
sumInputs = [P.Left (-2), P.Left 3, P.Right False, P.Right True]

adjunctionChecks :: [(String, Bool)]
adjunctionChecks =
  [ ( "Dual product adjunction transposes and returns both legs",
      sameOn ints (runOP dualProductArrow) (\n -> (n P.+ 1, P.even n))
        P.&& case leftToRight DualProduct DualDiagonal dualProductArrow of
          OP (l :×: r) -> sameOn ints l (P.+ 1) P.&& sameOn ints r P.even
    ),
    ( "Dual coproduct adjunction transposes and returns its arrow",
      let legs = rightToLeft DualSum DualDiagonal (OP sumArrow)
       in (case legs of OP (l :×: r) -> l 3 P.== "3" P.&& r True P.== "yes" P.&& r False P.== "no")
            P.&& sameOn sumInputs (runOP (leftToRight DualDiagonal DualSum legs)) sumArrow
    ),
    ( "Dual unit is the original counit",
      case unit (type '(DualDiagonal, DualProduct)) (type '(Int, Bool)) of
        OP (l :×: r) -> l (3, True) P.== 3 P.&& r (7, False) P.== False
    ),
    ( "Dual counit is the original unit",
      sameOn ints (runOP (counit (type '(DualProduct, DualDiagonal)) Int)) (\n -> (n, n))
    ),
    ( "Dual product adjunction left triangle",
      sameOn [(2, True), (-3, False)] (runOP (leftTriangle @DualProduct @DualDiagonal @'(Int, Bool))) (identity _)
    ),
    ( "Dual product adjunction right triangle",
      case rightTriangle @DualProduct @DualDiagonal @Int of
        OP (l :×: r) -> sameOn ints l (identity _) P.&& sameOn ints r (identity _)
    ),
    ( "Dual coproduct adjunction left triangle",
      case leftTriangle @DualDiagonal @DualSum @Int of
        OP (l :×: r) -> sameOn ints l (identity _) P.&& sameOn ints r (identity _)
    ),
    ( "Dual coproduct adjunction right triangle",
      sameOn sumInputs (runOP (rightTriangle @DualDiagonal @DualSum @'(Int, Bool))) (identity _)
    )
  ]

type Tensor p a b = Act p '(a, b)

pentagonShort,
  pentagonLong ::
    forall {k} (p :: BINARY_OP k) a b c d.
    (Associative p, a ∈ k, b ∈ k, c ∈ k, d ∈ k) =>
    k (Tensor p (Tensor p (Tensor p a b) c) d) (Tensor p a (Tensor p b (Tensor p c d)))
pentagonShort = rassoc p a b (Tensor p c d) ∘ rassoc p (Tensor p a b) c d
pentagonLong =
  map p (identity a :×: rassoc p b c d)
    ∘ rassoc p a (Tensor p b c) d
    ∘ map p (rassoc p a b c :×: identity d)

triangleDirect,
  triangleViaAssoc ::
    forall {k} (p :: BINARY_OP k) a b.
    (Monoidal p, a ∈ k, b ∈ k) =>
    k (Tensor p (Tensor p a (MonoidalEmpty p)) b) (Tensor p a b)
triangleDirect = map p (idr @_ @p @a :×: identity b)
triangleViaAssoc = map p (identity a :×: idl @_ @p @b) ∘ rassoc p a (MonoidalEmpty p) b

type Product = OpTensor (∧)

type Sum = OpTensor (∨)

tensorChecks :: [(String, Bool)]
tensorChecks =
  [ ( "Opposite tensor preserves argument order and composition",
      let f = OP ((P.+ 1) :: Int -> Int) :×: OP P.not
          g = OP ((P.* 3) :: Int -> Int) :×: OP (identity Bool)
          sample = (2, True)
       in runOP (map Product (g ∘ f)) sample P.== (7, False)
            P.&& runOP (map Product g ∘ map Product f) sample P.== (7, False)
            P.&& runOP (map Product (identity (type '(Int, Bool)))) sample P.== sample
    ),
    ( "Double opposite tensor acts like the original",
      unOpOp (map (OpTensor Product) (opOp ((P.+ 1) :: Int -> Int) :×: opOp P.not)) (2, True)
        P.== (3, False)
    ),
    ( "Opposite product associators are inverse in both directions",
      let l = lassoc Product Int Bool Char
          r = rassoc Product Int Bool Char
       in runOP (l ∘ r) ((3, True), 'x') P.== ((3, True), 'x')
            P.&& runOP (r ∘ l) (3, (True, 'x')) P.== (3, (True, 'x'))
    ),
    ( "Opposite coproduct associators preserve all branches in both round trips",
      let l = lassoc Sum Int Bool Char
          r = rassoc Sum Int Bool Char
          left = [P.Left (P.Left 3), P.Left (P.Right True), P.Right 'x']
          right = [P.Left 3, P.Right (P.Left True), P.Right (P.Right 'x')]
       in sameOn left (runOP (l ∘ r)) (identity _)
            P.&& sameOn right (runOP (r ∘ l)) (identity _)
    ),
    ( "Opposite product unitors are inverse on both sides",
      sameOn ints (runOP (idl @_ @Product @Int ∘ coidl @_ @Product @Int)) (identity _)
        P.&& sameOn [((), n) | n <- ints] (runOP (coidl @_ @Product @Int ∘ idl @_ @Product @Int)) (identity _)
        P.&& sameOn ints (runOP (idr @_ @Product @Int ∘ coidr @_ @Product @Int)) (identity _)
        P.&& sameOn [(n, ()) | n <- ints] (runOP (coidr @_ @Product @Int ∘ idr @_ @Product @Int)) (identity _)
    ),
    ( "Opposite coproduct unitors are inverse on both sides",
      sameOn ints (runOP (idl @_ @Sum @Int ∘ coidl @_ @Sum @Int)) (identity _)
        P.&& sameOn (P.map P.Right ints) (runOP (coidl @_ @Sum @Int ∘ idl @_ @Sum @Int)) (identity _)
        P.&& sameOn ints (runOP (idr @_ @Sum @Int ∘ coidr @_ @Sum @Int)) (identity _)
        P.&& sameOn (P.map P.Left ints) (runOP (coidr @_ @Sum @Int ∘ idr @_ @Sum @Int)) (identity _)
    ),
    ( "Opposite product pentagon",
      let sample = (3, (True, ('x', "end")))
          expected = (((3, True), 'x'), "end")
       in runOP (pentagonShort @Product @Int @Bool @Char @String) sample P.== expected
            P.&& runOP (pentagonLong @Product @Int @Bool @Char @String) sample P.== expected
    ),
    ( "Opposite coproduct pentagon",
      let samples = [P.Left 3, P.Right (P.Left True), P.Right (P.Right (P.Left 'x')), P.Right (P.Right (P.Right "end"))]
          expected = [P.Left (P.Left (P.Left 3)), P.Left (P.Left (P.Right True)), P.Left (P.Right 'x'), P.Right "end"]
       in P.map (runOP (pentagonShort @Sum @Int @Bool @Char @String)) samples P.== expected
            P.&& P.map (runOP (pentagonLong @Sum @Int @Bool @Char @String)) samples P.== expected
    ),
    ( "Opposite product triangle",
      runOP (triangleDirect @Product @Int @Bool) (3, True) P.== ((3, ()), True)
        P.&& runOP (triangleViaAssoc @Product @Int @Bool) (3, True) P.== ((3, ()), True)
    ),
    ( "Opposite coproduct triangle",
      let expected = [P.Left (P.Left (-2)), P.Left (P.Left 3), P.Right False, P.Right True]
       in P.map (runOP (triangleDirect @Sum @Int @Bool)) sumInputs P.== expected
            P.&& P.map (runOP (triangleViaAssoc @Sum @Int @Bool)) sumInputs P.== expected
    )
  ]

-- A ComonoidObject constraint must supply the evidence to compose and tensor
-- its operations in the original category, without extra Category/Obj premises.
coassociateLeft,
  coassociateRight ::
    forall {k} (p :: BINARY_OP k) m.
    (ComonoidObject p m) =>
    k m (Tensor p (Tensor p m m) m)
coassociateLeft = acting p (type '(m, m)) do
  map p (coappend p m :×: identity m) ∘ coappend p m
coassociateRight = acting p (type '(m, m)) do
  lassoc p m m m ∘ map p (identity m :×: coappend p m) ∘ coappend p m

coleftUnit,
  corightUnit ::
    forall {k} (p :: BINARY_OP k) m.
    (ComonoidObject p m) =>
    k m m
coleftUnit = idl @_ @p ∘ map p (coempty p m :×: identity m) ∘ coappend p m
corightUnit = idr @_ @p ∘ map p (identity m :×: coempty p m) ∘ coappend p m

comonoidChecks :: [(String, Bool)]
comonoidChecks =
  [ ( "Cartesian comonoid discards and copies",
      coempty (∧) Int 7 P.== () P.&& coappend (∧) Int 7 P.== (7, 7)
    ),
    ( "Cartesian comonoid coassociativity",
      sameOn ints (coassociateLeft @(∧) @Int) (coassociateRight @(∧) @Int)
        P.&& sameOn ints (coassociateLeft @(∧) @Int) (\n -> ((n, n), n))
    ),
    ( "Cartesian comonoid counit laws",
      sameOn ints (coleftUnit @(∧) @Int) (identity _)
        P.&& sameOn ints (corightUnit @(∧) @Int) (identity _)
    )
  ]

checks :: [(String, Bool)]
checks = functorChecks P.++ adjunctionChecks P.++ tensorChecks P.++ comonoidChecks
