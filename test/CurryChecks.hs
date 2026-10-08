module CurryChecks (checks) where

import AdjunctionChecks (OnlyTrue (..), OnlyUnit (..))
import Cats
import Data.Kind (Type)
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

-- Separate definitions on each side ensure the round trips work without
-- assuming that every curried input was originally produced by Curry₁.
type data PairLists :: (Types × Types) --> Types

type instance Act PairLists ab = (Fst ab, [Snd ab])

instance Functor PairLists where
  map _ (f :×: g) (a, bs) = (f a, P.map g bs)

type data WithList :: Type -> Types --> Types

type instance Act (WithList a) b = (a, [b])

instance Functor (WithList a) where
  map _ f (a, bs) = (a, P.map f bs)

type data CurriedLists :: Types --> (Types ^ Types)

type instance Act CurriedLists a = WithList a

instance Functor CurriedLists where
  map _ f = EXP \_ (a, bs) -> (f a, bs)

type data ListsPair :: (Types × Types) --> Types

type instance Act ListsPair ab = ([Snd ab], Fst ab)

instance Functor ListsPair where
  map _ (f :×: g) (bs, a) = (P.map g bs, f a)

swap :: PairLists ~> ListsPair
swap = EXP \_ (a, bs) -> (bs, a)

reversePairs, dropPairs :: PairLists ~> PairLists
reversePairs = EXP \_ (a, bs) -> (a, P.reverse bs)
dropPairs = EXP \_ (a, bs) -> (a, P.drop 1 bs)

reverseCurried, dropCurried :: CurriedLists ~> CurriedLists
reverseCurried = EXP \_ -> EXP \_ (a, bs) -> (a, P.reverse bs)
dropCurried = EXP \_ -> EXP \_ (a, bs) -> (a, P.drop 1 bs)

type C = Curry₀ @Types @Types @Types

type U = Uncurry₀ @Types @Types @Types

-- Abstract signatures verify that the equivalence is available beyond Types.
toFlatRoundTrip ::
  forall {a} {b} {c} (f :: (a × b) --> c).
  (Category a, Category b, Category c, Functor f) =>
  f ~> Uncurry₁ (Curry₁ f)
toFlatRoundTrip = unit (type '(Uncurry₀ @a @b @c, Curry₀ @a @b @c)) f

backToFlat ::
  forall {a} {b} {c} (f :: (a × b) --> c).
  (Category a, Category b, Category c, Functor f) =>
  Uncurry₁ (Curry₁ f) ~> f
backToFlat = counit (type '(Uncurry₀ @a @b @c, Curry₀ @a @b @c)) f

toCurried ::
  forall {a} {b} {c} (f :: a --> (c ^ b)).
  (Category a, Category b, Category c, Functor f) =>
  f ~> Curry₁ (Uncurry₁ f)
toCurried = unit (type '(Curry₀ @a @b @c, Uncurry₀ @a @b @c)) f

backToCurried ::
  forall {a} {b} {c} (f :: a --> (c ^ b)).
  (Category a, Category b, Category c, Functor f) =>
  Curry₁ (Uncurry₁ f) ~> f
backToCurried = counit (type '(Curry₀ @a @b @c, Uncurry₀ @a @b @c)) f

curriedArrow :: Curry₁ PairLists ~> CurriedLists
curriedArrow = EXP \_ -> EXP \_ (a, bs) -> (a, P.reverse bs)

flatArrow :: Uncurry₁ CurriedLists ~> PairLists
flatArrow = EXP \_ (a, bs) -> (a, P.drop 1 bs)

input :: (Int, [Bool])
input = (7, [True, False, False])

changed :: (String, [Int])
changed = ("7", [1, 0, 0])

type Mixed = FstFunctor @OnlyTrue @OnlyUnit

type MC = Curry₀ @OnlyTrue @OnlyUnit @OnlyTrue

type MU = Uncurry₀ @OnlyTrue @OnlyUnit @OnlyTrue

checks :: [(String, Bool)]
checks =
  [ ( "Curry₂ maps only the remaining argument",
      map (Curry₂ PairLists Int) P.fromEnum input P.== (7, [1, 0, 0])
    ),
    ( "Curry₁ maps the fixed argument naturally",
      (map (Curry₁ PairLists) P.show $$ Bool) input P.== ("7", [True, False, False])
    ),
    ( "Uncurry₁ maps both arguments of an independent curried functor",
      map (Uncurry₁ CurriedLists) (P.show :×: P.fromEnum) input P.== changed
    ),
    ( "Uncurry₁ preserves identity",
      map (Uncurry₁ CurriedLists) (identity (type '(Int, Bool))) input P.== input
    ),
    ( "Uncurry₁ preserves composition order",
      let first = (P.+ 1) :×: P.not
          second = (P.* 3) :×: P.fromEnum
       in map (Uncurry₁ CurriedLists) (second ∘ first) input
            P.== (map (Uncurry₁ CurriedLists) second ∘ map (Uncurry₁ CurriedLists) first) input
            P.&& map (Uncurry₁ CurriedLists) (second ∘ first) input P.== (24, [0, 1, 1])
    ),
    ( "Curry₀ preserves identity on transformations",
      ((map C (identity PairLists) $$ Int) $$ Bool) input P.== input
    ),
    ( "Curry₀ preserves noncommuting transformation composition",
      ((map C (dropPairs ∘ reversePairs) $$ Int) $$ Bool) input
        P.== (((map C dropPairs ∘ map C reversePairs) $$ Int) $$ Bool) input
        P.&& ((map C (dropPairs ∘ reversePairs) $$ Int) $$ Bool) input P.== (7, [False, True])
    ),
    ( "Curry₀ changes functor tags",
      ((map C swap $$ Int) $$ Bool) input P.== ([True, False, False], 7)
    ),
    ( "Uncurry₀ preserves identity on transformations",
      (map U (identity CurriedLists) $$ (Int, Bool)) input P.== input
    ),
    ( "Uncurry₀ preserves noncommuting transformation composition",
      (map U (dropCurried ∘ reverseCurried) $$ (Int, Bool)) input
        P.== ((map U dropCurried ∘ map U reverseCurried) $$ (Int, Bool)) input
        P.&& (map U (dropCurried ∘ reverseCurried) $$ (Int, Bool)) input P.== (7, [False, True])
    ),
    ( "Uncurrying after currying preserves a binary functor's arrow action",
      map (Uncurry₁ (Curry₁ PairLists)) (P.show :×: P.fromEnum) input
        P.== map PairLists (P.show :×: P.fromEnum) input
    ),
    ( "Currying after uncurrying preserves both curried arrow actions",
      (map (Curry₁ (Uncurry₁ CurriedLists)) P.show $$ Bool) input
        P.== (map CurriedLists P.show $$ Bool) input
        P.&& map (Act (Curry₁ (Uncurry₁ CurriedLists)) Int) P.fromEnum input
          P.== map (Act CurriedLists Int) P.fromEnum input
    ),
    ( "Flat equivalence witnesses are inverse in both orders",
      ((backToFlat @PairLists ∘ toFlatRoundTrip @PairLists) $$ (Int, Bool)) input P.== input
        P.&& ((toFlatRoundTrip @PairLists ∘ backToFlat @PairLists) $$ (Int, Bool)) input P.== input
    ),
    ( "Curried equivalence witnesses are inverse in both orders",
      (((backToCurried @CurriedLists ∘ toCurried @CurriedLists) $$ Int) $$ Bool) input P.== input
        P.&& (((toCurried @CurriedLists ∘ backToCurried @CurriedLists) $$ Int) $$ Bool) input P.== input
    ),
    ( "Flat equivalence is natural in the functor argument",
      ((toFlatRoundTrip @ListsPair ∘ swap) $$ (Int, Bool)) input
        P.== ((map U (map C swap) ∘ toFlatRoundTrip @PairLists) $$ (Int, Bool)) input
    ),
    ( "Curried equivalence is natural in the functor argument",
      (((toCurried @CurriedLists ∘ reverseCurried) $$ Int) $$ Bool) input
        P.== (((map C (map U reverseCurried) ∘ toCurried @CurriedLists) $$ Int) $$ Bool) input
    ),
    ( "Currying adjunction transposition round trip",
      (((rightToLeft U C (leftToRight C U curriedArrow)) $$ Int) $$ Bool) input
        P.== ((curriedArrow $$ Int) $$ Bool) input
    ),
    ( "Uncurrying adjunction transposition round trip",
      (rightToLeft C U (leftToRight U C flatArrow) $$ (Int, Bool)) input
        P.== (flatArrow $$ (Int, Bool)) input
    ),
    ( "Currying adjunction left triangle",
      let triangle = counit (type '(C, U)) (Curry₁ PairLists) ∘ map C (unit (type '(U, C)) PairLists)
       in ((triangle $$ Int) $$ Bool) input P.== input
    ),
    ( "Currying adjunction right triangle",
      let triangle = map U (counit (type '(C, U)) CurriedLists) ∘ unit (type '(U, C)) (Uncurry₁ CurriedLists)
       in (triangle $$ (Int, Bool)) input P.== input
    ),
    ( "Uncurrying adjunction left triangle",
      let triangle = counit (type '(U, C)) (Uncurry₁ CurriedLists) ∘ map U (unit (type '(C, U)) CurriedLists)
       in (triangle $$ (Int, Bool)) input P.== input
    ),
    ( "Uncurrying adjunction right triangle",
      let triangle = map C (counit (type '(U, C)) PairLists) ∘ unit (type '(C, U)) (Curry₁ PairLists)
       in ((triangle $$ Int) $$ Bool) input P.== input
    ),
    ( "Curry and uncurry retain different constrained object kinds",
      case ( map (Uncurry₁ (Curry₁ Mixed)) (TArrow (P.* 3) :×: UArrow (P.+ 2)),
             toFlatRoundTrip @Mixed $$ (type '( 'True, '())),
             backToFlat @Mixed $$ (type '( 'True, '()))
           ) of
        (TArrow mapped, TArrow forward, TArrow backward) ->
          P.all (\n -> mapped n P.== 3 P.* n P.&& forward n P.== n P.&& backward n P.== n) [-3 .. 3]
    ),
    ( "Higher curry/uncurry transformations preserve constrained indices",
      case (map MU (map MC (identity Mixed)) $$ (type '( 'True, '()))) of
        TArrow f -> P.all (\n -> f n P.== n) [-3 .. 3]
    )
  ]
