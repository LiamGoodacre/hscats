module AdjunctionChecks (checks, Env, Reader) where

import Cats
import Data.Kind (Type)
import Data.Type.Equality (type (~))
import Prelude (Bool (..), Int, String)
import Prelude qualified as P

type data Env :: Type -> Types --> Types
type instance Act (Env s) a = (a, s)

instance Functor (Env s) where
  map _ h (a, s) = (h a, s)

type data Reader :: Type -> Types --> Types
type instance Act (Reader s) a = s -> a

instance Functor (Reader s) where
  map _ h k = h ∘ k

instance Env s ⊣ Reader s where
  leftToRight _ _ h a s = h (a, s)
  rightToLeft _ _ k (a, s) = k a s

-- The abstract signatures check that the class propagates object evidence.
leftRoundTrip ::
  forall {c} {d} (f :: c --> d) g a b.
  (f ⊣ g, a ∈ c, b ∈ d) =>
  d (Act f a) b -> d (Act f a) b
leftRoundTrip h = rightToLeft g f (leftToRight f g h :: c a (Act g b))

rightRoundTrip ::
  forall {c} {d} (f :: c --> d) g a b.
  (f ⊣ g, a ∈ c, b ∈ d) =>
  c a (Act g b) -> c a (Act g b)
rightRoundTrip k = leftToRight f g (rightToLeft g f k :: d (Act f a) b)

leftNaturality ::
  forall {c} {d} (f :: c --> d) g a' a b b'.
  (f ⊣ g, a' ∈ c, a ∈ c, b ∈ d, b' ∈ d) =>
  c a' a -> d b b' -> d (Act f a) b ->
  (c a' (Act g b'), c a' (Act g b'))
leftNaturality p q h =
  ( leftToRight f g (q ∘ h ∘ map f p),
    map g q ∘ leftToRight f g h ∘ p
  )

rightNaturality ::
  forall {c} {d} (f :: c --> d) g a' a b b'.
  (f ⊣ g, a' ∈ c, a ∈ c, b ∈ d, b' ∈ d) =>
  c a' a -> d b b' -> c a (Act g b) ->
  (d (Act f a') b', d (Act f a') b')
rightNaturality p q k =
  ( rightToLeft g f (map g q ∘ k ∘ p),
    q ∘ rightToLeft g f k ∘ map f p
  )

leftTriangle ::
  forall {c} {d} (f :: c --> d) g a.
  (f ⊣ g, a ∈ c) => d (Act f a) (Act f a)
leftTriangle = counit (type '(f, g)) (Act f a) ∘ map f (unit (type '(g, f)) a)

rightTriangle ::
  forall {c} {d} (f :: c --> d) g b.
  (f ⊣ g, b ∈ d) => c (Act g b) (Act g b)
rightTriangle = map g (counit (type '(f, g)) b) ∘ unit (type '(g, f)) (Act g b)

-- Equivalent categories with different object-name kinds. Only one object
-- is valid in each; arrows are arbitrary Int functions and need not commute.
data OnlyTrue :: CATEGORY Bool where
  TArrow :: (Int -> Int) -> OnlyTrue 'True 'True

data OnlyUnit :: CATEGORY () where
  UArrow :: (Int -> Int) -> OnlyUnit '() '()

type instance Obj OnlyTrue a = a ~ 'True
type instance Obj OnlyUnit a = a ~ '()

instance Semigroupoid OnlyTrue where
  TArrow f ∘ TArrow g = TArrow (f ∘ g)

instance Category OnlyTrue where
  identity _ = TArrow P.id

instance Semigroupoid OnlyUnit where
  UArrow f ∘ UArrow g = UArrow (f ∘ g)

instance Category OnlyUnit where
  identity _ = UArrow P.id

type data ToUnit :: OnlyTrue --> OnlyUnit
type instance Act ToUnit a = '()

type data ToTrue :: OnlyUnit --> OnlyTrue
type instance Act ToTrue a = 'True

instance Functor ToUnit where
  map _ (TArrow h) = UArrow h

instance Functor ToTrue where
  map _ (UArrow h) = TArrow h

instance ToUnit ⊣ ToTrue where
  leftToRight _ _ (UArrow h) = TArrow h
  rightToLeft _ _ (TArrow h) = UArrow h

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs h k = P.all (\x -> h x P.== k x) xs

ints :: [Int]
ints = [-3 .. 3]

flags :: [Bool]
flags = [False, True]

envs :: [(Int, Bool)]
envs = [(n, b) | n <- ints, b <- flags]

envArrow :: (Int, Bool) -> Int
envArrow (n, b) = if b then 2 P.* n P.+ 1 else n P.- 3

readerArrow :: Int -> Bool -> Int
readerArrow n b = if b then n P.* n else 3 P.- n

checks :: [(String, Bool)]
checks =
  [ ( "Adjunction left transpose round trip",
      sameOn envs (leftRoundTrip @(Env Bool) @(Reader Bool) envArrow) envArrow
    ),
    ( "Adjunction right transpose round trip",
      P.and [rightRoundTrip @(Env Bool) @(Reader Bool) readerArrow n b P.== readerArrow n b | (n, b) <- envs]
    ),
    ( "Adjunction left transpose naturality at both endpoints",
      let (l, r) = leftNaturality @(Env Bool) @(Reader Bool) P.fromEnum P.show envArrow
       in P.and [l a b P.== r a b | a <- flags, b <- flags]
    ),
    ( "Adjunction right transpose naturality at both endpoints",
      let (l, r) = rightNaturality @(Env Bool) @(Reader Bool) P.fromEnum P.show readerArrow
       in sameOn [(a, b) | a <- flags, b <- flags] l r
    ),
    ( "Adjunction unit naturality changes result type",
      let l = map (Reader Bool) (map (Env Bool) P.show) ∘ unit (type '(Reader Bool, Env Bool)) Int
          r = unit (type '(Reader Bool, Env Bool)) String ∘ P.show
       in P.and [l n b P.== r n b | (n, b) <- envs]
    ),
    ( "Adjunction counit naturality changes result type",
      let l = P.show ∘ counit (type '(Env Bool, Reader Bool)) Int
          r = counit (type '(Env Bool, Reader Bool)) String ∘ map (Env Bool) (map (Reader Bool) P.show)
       in sameOn [(readerArrow n, b) | (n, b) <- envs] l r
    ),
    ( "Adjunction left triangle",
      sameOn envs (leftTriangle @(Env Bool) @(Reader Bool) @Int) P.id
    ),
    ( "Adjunction right triangle",
      P.and [rightTriangle @(Env Bool) @(Reader Bool) @Int (readerArrow n) b P.== readerArrow n b | (n, b) <- envs]
    ),
    ( "Constrained adjunction transpose round trips with different object kinds",
      case (leftRoundTrip @ToUnit @ToTrue (UArrow (P.+ 2)), rightRoundTrip @ToUnit @ToTrue (TArrow (P.* 3))) of
        (UArrow l, TArrow r) -> sameOn ints l (P.+ 2) P.&& sameOn ints r (P.* 3)
    ),
    ( "Constrained adjunction left naturality with noncommuting arrows",
      case leftNaturality @ToUnit @ToTrue (TArrow (P.+ 1)) (UArrow (P.* 3)) (UArrow (\n -> n P.* n)) of
        (TArrow l, TArrow r) -> sameOn ints l r P.&& sameOn ints l (\n -> 3 P.* (n P.+ 1) P.* (n P.+ 1))
    ),
    ( "Constrained adjunction right naturality with noncommuting arrows",
      case rightNaturality @ToUnit @ToTrue (TArrow (P.* 3)) (UArrow (P.+ 1)) (TArrow (\n -> n P.* n)) of
        (UArrow l, UArrow r) -> sameOn ints l r P.&& sameOn ints l (\n -> (3 P.* n) P.* (3 P.* n) P.+ 1)
    ),
    ( "Constrained adjunction triangles",
      case (leftTriangle @ToUnit @ToTrue @'True, rightTriangle @ToUnit @ToTrue @'()) of
        (UArrow l, TArrow r) -> sameOn ints l P.id P.&& sameOn ints r P.id
    ),
    ( "Product adjunction left transpose naturality",
      let (l, r) = leftNaturality @(Δ₂ Types) @(∧)
            P.fromEnum (P.length :×: P.not) ((P.show :: Int -> String) :×: P.even)
       in sameOn flags l r P.&& sameOn flags l (\b -> (1, b))
    ),
    ( "Coproduct adjunction left transpose naturality",
      let h = P.either (P.show :: Int -> String) (\b -> if b then "yes" else "no")
       in case leftNaturality @(∨) @(Δ₂ Types) (P.fromEnum :×: (P.== 'x')) P.length h of
            (l1 :×: l2, r1 :×: r2) -> sameOn flags l1 r1 P.&& sameOn ['x', 'y'] l2 r2
    )
  ]
