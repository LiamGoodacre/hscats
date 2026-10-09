-- | Representable adjunction and Coyoneda encoding experiments.
module RepresentableExamples where

import Cats
import Data.Kind (Type)
import Prelude qualified

type data ArrTo :: forall (k :: CATEGORY i) -> i -> Op k --> Types

type instance Act (ArrTo k r) a = k a r

instance (Category k, r ∈ k) => Functor (ArrTo k r) where
  map _ (OP ba) = (∘ ba)

type data OpArrTo :: forall (k :: CATEGORY i) -> i -> k --> Op Types

type instance Act (OpArrTo k r) a = k a r

instance (Category k, r ∈ k) => Functor (OpArrTo k r) where
  map _ ba = OP (∘ ba)

instance OpArrTo Types r ⊣ ArrTo Types r where
  rightToLeft _ _ = OP ∘ Prelude.flip
  leftToRight _ _ = Prelude.flip ∘ runOP

{- coyoneda -}

data DataCoyoneda :: forall k. (k --> Types) -> NamesOf k -> Type where
  MakeDataCoyoneda :: (a ∈ k) => Act f a -> k a b -> DataCoyoneda @k f b

type data Coyoneda :: (k --> Types) -> (k --> Types)

type instance Act (Coyoneda f) x = DataCoyoneda f x

instance (Category k) => Functor (Coyoneda @k f) where
  map _ ab (MakeDataCoyoneda fx xa) = MakeDataCoyoneda fx (ab ∘ xa)

lowerCoyoneda :: forall {k} (f :: k --> Types) b. (Functor f, b ∈ k) => DataCoyoneda f b -> Act f b
lowerCoyoneda (MakeDataCoyoneda value arrow) = map f arrow value

type Lists = Constructor []

sample :: DataCoyoneda Lists Prelude.Int
sample = MakeDataCoyoneda [1, 2, 3] (Prelude.+ 1)

curried :: Prelude.Int -> Prelude.Bool -> Prelude.Int
curried n b = if b then n Prelude.+ 3 else 2 Prelude.* n

checks :: [(Prelude.String, Prelude.Bool)]
checks =
  [ ( "Representable adjunction transpose round trip",
      let result =
            leftToRight
              (OpArrTo Types Prelude.Int)
              (ArrTo Types Prelude.Int)
              (rightToLeft (ArrTo Types Prelude.Int) (OpArrTo Types Prelude.Int) curried)
       in Prelude.and [result n b Prelude.== curried n b | n <- [-3 .. 3], b <- [Prelude.False, Prelude.True]]
    ),
    ( "Representable adjunction reverses function arguments",
      case rightToLeft (ArrTo Types Prelude.Int) (OpArrTo Types Prelude.Int) curried of
        OP result -> result Prelude.True 7 Prelude.== 10 Prelude.&& result Prelude.False 7 Prelude.== 14
    ),
    ("Coyoneda lowers its stored arrow", lowerCoyoneda sample Prelude.== [2, 3, 4]),
    ("Coyoneda mapping changes the result type", lowerCoyoneda (map (Coyoneda Lists) Prelude.show sample) Prelude.== ["2", "3", "4"]),
    ("Coyoneda defers composed maps", lowerCoyoneda (map (Coyoneda Lists) ((Prelude.* 3) ∘ (Prelude.+ 1)) sample) Prelude.== [9, 12, 15])
  ]
