module MonadChecks (checks) where

import AdjunctionChecks (Env, OnlyTrue (..), OnlyUnit (..), Reader, ToTrue, ToUnit)
import Cats
import Cats.Adjoint
import Cats.Do qualified as Do
import Cats.Monad qualified as Monad
import Prelude (Bool (..), Int, Maybe (..), String)
import Prelude qualified as P

type Lists = TypeConstructor []

type Optional = TypeConstructor Maybe

type State = ViaAdjunction (Reader Int • Env Int)

type Store = ViaAdjunction (Env Int • Reader Int)

-- Independent instances need no adjunction or decomposition. This comonad
-- keeps a fixed context; the composition instance below also ensures the
-- adjunction bridge leaves clients free to choose their own instances.
type data Context :: Types --> Types

type instance Act Context a = (String, a)

instance Functor Context where
  map _ f (s, a) = (s, f a)

instance MonoidObject (OpTensor Composing) Context where
  empty _ _ = OP (EXP \_ -> P.snd)
  append _ _ = OP (EXP \_ (s, a) -> (s, (s, a)))

type data Identity :: Types --> Types

type instance Act Identity a = a

instance Functor Identity where
  map _ f = f

instance Identity ⊣ Identity where
  leftToRight _ _ f = f
  rightToLeft _ _ f = f

instance MonoidObject Composing (Identity • Identity) where
  empty _ _ = EXP \_ -> P.id
  append _ _ = EXP \_ -> P.id

instance MonoidObject (OpTensor Composing) (Identity • Identity) where
  empty _ _ = OP (EXP \_ -> P.id)
  append _ _ = OP (EXP \_ -> P.id)

-- These signatures must work with abstract constraints, not merely with
-- concrete tags whose instances could hide missing evidence in the aliases.
unitFromAlias ::
  forall {c} (m :: c --> c) a.
  (AdjunctionMonad m, a ∈ c) => c a (Act m a)
unitFromAlias = Monad.unit (ViaAdjunction m) a

unitFromBy ::
  forall {c} d (m :: c --> c) a.
  (AdjunctionMonadBy m d, a ∈ c) => c a (Act m a)
unitFromBy = Monad.unit (ViaAdjunction m) a

counitFromAlias ::
  forall {c} (w :: c --> c) a.
  (AdjunctionComonad w, a ∈ c) => c (Act w a) a
counitFromAlias = Monad.counit (ViaAdjunction w) a

counitFromBy ::
  forall {c} d (w :: c --> c) a.
  (AdjunctionComonadBy w d, a ∈ c) => c (Act w a) a
counitFromBy = Monad.counit (ViaAdjunction w) a

stateDecomposition :: Decompose (Reader Int • Env Int) :~: '(Reader Int, Env Int)
stateDecomposition = Refl

mixedDecomposition :: Decompose (ToTrue • ToUnit) :~: '(ToTrue, ToUnit)
mixedDecomposition = Refl

mixedInner :: Inner (ToTrue • ToUnit) :~: ToUnit
mixedInner = Refl

mixedOuter :: Outer (ToTrue • ToUnit) :~: ToTrue
mixedOuter = Refl

mixedMiddle :: MidComposition (ToTrue • ToUnit) :~: OnlyUnit
mixedMiddle = Refl

mixedRecomposition :: TheComposition (ToTrue • ToUnit) :~: (ToTrue • ToUnit)
mixedRecomposition = Refl

ints :: [Int]
ints = [-3 .. 3]

lists :: [[Int]]
lists = [[], [0], [-2, 1, 3]]

nestedLists :: [[[Int]]]
nestedLists = [[], [[]], [[1, 2], [], [3]], [[-2], [0, 4]]]

step :: Int -> [Int]
step n = [n P.+ 1, 3 P.* n]

next :: Int -> [String]
next n = [P.show n, P.show (n P.* n)]

-- Both the result and the updated state depend on the incoming state.
transition :: Int -> (Int, Int)
transition s = (2 P.* s P.+ 1, s P.+ 3)

stateStep :: Int -> Int -> (String, Int)
stateStep n s = (P.show (n P.+ s), 2 P.* s)

stateNext :: String -> Int -> (Int, Int)
stateNext str s = (P.length str P.+ s, s P.- 1)

sameOn :: (P.Eq b) => [a] -> (a -> b) -> (a -> b) -> Bool
sameOn xs f g = P.all (\x -> f x P.== g x) xs

store :: (Int -> Int, Int)
store = (\n -> n P.* n P.+ 2, 1)

observeStore :: (Int -> a, Int) -> (Int, [a])
observeStore (peek, pos) = (pos, P.map peek ints)

observeDouble :: (Int -> (Int -> a, Int), Int) -> (Int, [(Int, [a])])
observeDouble (peek, pos) = (pos, P.map (observeStore ∘ peek) ints)

observeTriple :: (Int -> (Int -> (Int -> a, Int), Int), Int) -> (Int, [(Int, [(Int, [a])])])
observeTriple (peek, pos) = (pos, P.map (observeDouble ∘ peek) ints)

checks :: [(String, Bool)]
checks =
  [ ("Constructor list monad unit", Monad.unit Lists Int 7 P.== [7]),
    ("Constructor list monad join preserves order", Monad.join Lists Int [[1, 2], [], [3]] P.== [1, 2, 3]),
    ("Constructor list flatMap", P.all (\xs -> Monad.flatMap Lists step xs P.== P.concatMap step xs) lists),
    ("List monad left unit", P.all (\n -> Monad.flatMap Lists step (Monad.unit Lists Int n) P.== step n) ints),
    ("List monad right unit", P.all (\xs -> Monad.flatMap Lists (Monad.unit Lists Int) xs P.== xs) lists),
    ( "List monad bind associativity changes result type",
      P.all (\xs -> Monad.flatMap Lists next (Monad.flatMap Lists step xs) P.== Monad.flatMap Lists (Monad.flatMap Lists next ∘ step) xs) lists
    ),
    ( "List monad multiplication associativity",
      P.all
        (\xs -> Monad.join Lists Int (Monad.join Lists (type [Int]) xs) P.== Monad.join Lists Int (map Lists (Monad.join Lists Int) xs))
        [[], [[]], nestedLists, [nestedLists P.!! 2, nestedLists P.!! 3]]
    ),
    ( "List monad unit naturality",
      P.all (\n -> map Lists P.show (Monad.unit Lists Int n) P.== Monad.unit Lists String (P.show n)) ints
    ),
    ( "List monad multiplication naturality",
      P.all (\xs -> map Lists P.show (Monad.join Lists Int xs) P.== Monad.join Lists String (map (Lists • Lists) P.show xs)) nestedLists
    ),
    ( "Constructor Maybe handles absent computations",
      Monad.unit Optional Int 7 P.== Just 7
        P.&& Monad.join Optional Int (Just Nothing) P.== Nothing
        P.&& Monad.flatMap Optional (\(n :: Int) -> if n P.> 0 then Just (P.show n) else Nothing) (Just 3) P.== Just "3"
        P.&& Monad.flatMap Optional (Just ∘ P.show) (Nothing :: Maybe Int) P.== Nothing
    ),
    ( "Qualified do supports a general list monad",
      ( Do.with Lists Do.do
          x <- [1, 2 :: Int]
          y <- [10, 20 :: Int]
          Do.pure (x P.+ y)
      )
        P.== [11, 21, 12, 22]
    ),
    ( "Qualified do supports sequencing",
      ( Do.with Lists Do.do
          [(), ()]
          Do.pure (3 :: Int)
      )
        P.== [3, 3]
    ),
    ( "Qualified do handles Maybe failure",
      ( Do.with Optional Do.do
          x <- Nothing :: Maybe Int
          Do.pure (x P.+ 1)
      )
        P.== Nothing
    ),
    ( "Nested qualified do selects independent monads",
      ( Do.with Lists Do.do
          x <- [1, 2 :: Int]
          let inner = Do.with Optional Do.do
                y <- Just (x P.+ 10)
                Do.pure (P.show y)
          Do.pure inner
      )
        P.== [Just "11", Just "12"]
    ),
    ( "Adjunction state unit and multiplication agree with direct operations",
      let nested s = (transition, s P.+ 2)
       in sameOn ints (Monad.unit State Int 7) (unit (type '(Reader Int, Env Int)) Int 7)
            P.&& sameOn ints (Monad.join State Int nested) (join (type '(Reader Int, Env Int)) Int nested)
    ),
    ( "State bind retains state sequencing",
      sameOn ints (Monad.flatMap State stateStep transition) (\s -> (P.show (3 P.* s P.+ 4), 2 P.* (s P.+ 3)))
    ),
    ( "State monad left and right units",
      sameOn ints (Monad.flatMap State stateStep (Monad.unit State Int 5)) (stateStep 5)
        P.&& sameOn ints (Monad.flatMap State (Monad.unit State Int) transition) transition
    ),
    ( "State monad associativity",
      sameOn
        ints
        (Monad.flatMap State stateNext (Monad.flatMap State stateStep transition))
        (Monad.flatMap State (\n -> Monad.flatMap State stateNext (stateStep n)) transition)
    ),
    ( "Independent composition instances coexist with the adjunction bridge",
      Monad.unit (Identity • Identity) Int 7 P.== Monad.unit (ViaAdjunction (Identity • Identity)) Int 7
        P.&& Monad.join (Identity • Identity) Int 9 P.== Monad.join (ViaAdjunction (Identity • Identity)) Int 9
        P.&& Monad.counit (Identity • Identity) Int 3 P.== Monad.counit (ViaAdjunction (Identity • Identity)) Int 3
        P.&& Monad.duplicate (Identity • Identity) Int 5 P.== Monad.duplicate (ViaAdjunction (Identity • Identity)) Int 5
    ),
    ( "Independent context comonad extraction and duplication",
      Monad.counit Context Int ("ctx", 7) P.== 7
        P.&& Monad.duplicate Context Int ("ctx", 7) P.== ("ctx", ("ctx", 7))
    ),
    ( "Comonad extension has access to the context",
      Monad.extend Context (\(s, n) -> P.show n P.++ s) ("ctx", 7 :: Int) P.== ("ctx", "7ctx")
    ),
    ( "Context comonad counit laws",
      P.all
        ( \x ->
            Monad.counit Context (type (String, Int)) (Monad.duplicate Context Int x) P.== x
              P.&& map Context (Monad.counit Context Int) (Monad.duplicate Context Int x) P.== x
        )
        [("ctx", n) | n <- ints]
    ),
    ( "Context comonad coassociativity",
      P.all
        ( \x ->
            Monad.duplicate Context (type (String, Int)) (Monad.duplicate Context Int x)
              P.== map Context (Monad.duplicate Context Int) (Monad.duplicate Context Int x)
        )
        [("ctx", n) | n <- ints]
    ),
    ( "Context comonad operations are natural",
      P.all
        ( \x ->
            P.show (Monad.counit Context Int x) P.== Monad.counit Context String (map Context P.show x)
              P.&& map (Context • Context) P.show (Monad.duplicate Context Int x)
                P.== Monad.duplicate Context String (map Context P.show x)
        )
        [("ctx", n) | n <- ints]
    ),
    ( "Store comonad operations agree with the adjunction",
      Monad.counit Store Int store P.== counit (type '(Env Int, Reader Int)) Int store
        P.&& observeDouble (Monad.duplicate Store Int store)
          P.== observeDouble (duplicate (type '(Env Int, Reader Int)) Int store)
    ),
    ( "Store comonad counit laws preserve every observed position",
      observeStore (Monad.counit Store (type (Int -> Int, Int)) (Monad.duplicate Store Int store)) P.== observeStore store
        P.&& observeStore (map Store (Monad.counit Store Int) (Monad.duplicate Store Int store)) P.== observeStore store
    ),
    ( "Store comonad coassociativity preserves nested positions",
      observeTriple (Monad.duplicate Store (type (Int -> Int, Int)) (Monad.duplicate Store Int store))
        P.== observeTriple (map Store (Monad.duplicate Store Int) (Monad.duplicate Store Int store))
    ),
    ( "Store extension evaluates neighboring contexts",
      observeStore (Monad.extend Store (\(peek, pos) -> peek (pos P.- 1) P.+ peek (pos P.+ 1)) store)
        P.== (1, P.map (\n -> 2 P.* n P.* n P.+ 6) ints)
    ),
    ( "Composition decomposition supports different object-name kinds",
      case (stateDecomposition, mixedDecomposition, mixedInner, mixedOuter, mixedMiddle, mixedRecomposition) of
        (Refl, Refl, Refl, Refl, Refl, Refl) -> True
    ),
    ( "Abstract adjunction monad aliases supply the bridge",
      sameOn ints (unitFromAlias @(Reader Int • Env Int) @Int 7) (\s -> (7, s))
        P.&& sameOn ints (unitFromBy @Types @(Reader Int • Env Int) @Int 7) (\s -> (7, s))
    ),
    ( "Abstract adjunction comonad aliases supply the bridge",
      counitFromAlias @(Env Int • Reader Int) @Int store P.== 3
        P.&& counitFromBy @Types @(Env Int • Reader Int) @Int store P.== 3
    ),
    ( "Monad aliases support a different intermediate object kind",
      case (unitFromAlias @(ToTrue • ToUnit) @'True, unitFromBy @OnlyUnit @(ToTrue • ToUnit) @'True) of
        (TArrow l, TArrow r) -> sameOn ints l P.id P.&& sameOn ints r P.id
    ),
    ( "Comonad aliases support a different intermediate object kind",
      case (counitFromAlias @(ToUnit • ToTrue) @'(), counitFromBy @OnlyTrue @(ToUnit • ToTrue) @'()) of
        (UArrow l, UArrow r) -> sameOn ints l P.id P.&& sameOn ints r P.id
    ),
    ( "Generic flatMap and extend retain constrained object evidence",
      case (Monad.flatMap (ViaAdjunction (ToTrue • ToUnit)) (TArrow (P.+ 3)), Monad.extend (ViaAdjunction (ToUnit • ToTrue)) (UArrow (P.* 2))) of
        (TArrow l, UArrow r) -> sameOn ints l (P.+ 3) P.&& sameOn ints r (P.* 2)
    )
  ]
