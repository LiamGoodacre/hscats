-- | Small categories and the single-object monoid encoding.
module CategoryExamples where

import Cats
import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (~))
import Prelude (($))
import Prelude qualified

{- Monoid: definition -}

-- Monoids are categories with a single object
type Monoid :: CATEGORY i -> i -> Constraint
class (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

instance (Category c, o ∈ c, forall x. (x ∈ c) => (x ~ o)) => Monoid c o

{- Monoid: examples -}

data PreludeMonoid :: Type -> CATEGORY () where
  PreludeMonoid :: {getPreludeMonoid :: m} -> PreludeMonoid m '() '()

type instance Obj (PreludeMonoid m) x = (x ~ '())

instance (Prelude.Semigroup m) => Semigroupoid (PreludeMonoid m) where
  PreludeMonoid l ∘ PreludeMonoid r = PreludeMonoid (l Prelude.<> r)

instance (Prelude.Monoid m) => Category (PreludeMonoid m) where
  identity _ = PreludeMonoid Prelude.mempty

boring_monoid_category_example :: ()
boring_monoid_category_example = ()
  where
    _monoid_mappend :: (Monoid c o) => c o o -> c o o -> c o o
    _monoid_mappend = (∘)

    _monoid_mempty :: (Monoid c o) => c o o
    _monoid_mempty = identity _

    _eg0 :: [Prelude.Integer]
    _eg0 = getPreludeMonoid _monoid_mempty

    _eg1 :: [Prelude.Integer]
    _eg1 = getPreludeMonoid $ PreludeMonoid [1] `_monoid_mappend` PreludeMonoid [2, 3]

data Endo :: i -> CATEGORY i -> CATEGORY () where
  ENDO :: c o o -> Endo o c '() '()

type instance Obj (Endo o c) x = (x ~ '())

instance (Semigroupoid c, o ∈ c) => Semigroupoid (Endo o c) where
  ENDO l ∘ ENDO r = ENDO (l ∘ r)

instance (Category c, o ∈ c) => Category (Endo o c) where
  identity _ = ENDO (identity _)

{- Category: 1 -}

data One :: CATEGORY () where
  ONE :: One '() '()

type instance Obj One t = (t ~ '())

instance Semigroupoid One where
  ONE ∘ ONE = ONE

instance Category One where
  identity () = ONE

-- Natural numbers
data N = S N | Z

-- "Less than or equal to for Natural numbers" forms a category
data (≤) :: CATEGORY N where
  E :: n ≤ n
  B :: l ≤ u -> l ≤ 'S u

type CanonicalN :: N -> N
type family CanonicalN n where
  CanonicalN 'Z = 'Z
  CanonicalN ('S k) = 'S (CanonicalN k)

type instance Obj (≤) x = x ~ CanonicalN x

instance Semigroupoid (≤) where
  E ∘ r = r
  B l ∘ r = B (l ∘ r)

instance Category (≤) where
  identity _ = E

steps :: a ≤ b -> Prelude.Int
steps E = 0
steps (B rest) = 1 Prelude.+ steps rest

twoSteps :: 'Z ≤ 'S ('S 'Z)
twoSteps = B E ∘ B E

checks :: [(Prelude.String, Prelude.Bool)]
checks =
  [ ("Single-object monoid identity", getPreludeMonoid (identity (type '())) Prelude.== ([] :: [Prelude.Int])),
    ("Single-object monoid composition order", getPreludeMonoid (PreludeMonoid [1 :: Prelude.Int] ∘ PreludeMonoid [2, 3]) Prelude.== [1, 2, 3]),
    ("Endomorphism category retains its object", case ENDO ((Prelude.* 3) :: Prelude.Int -> Prelude.Int) ∘ ENDO (Prelude.+ 1) of ENDO f -> f 7 Prelude.== 24),
    ("Natural-number arrows compose", steps twoSteps Prelude.== 2),
    ("Natural-number identities preserve arrows", steps (identity (type ('S ('S 'Z))) ∘ twoSteps ∘ identity (type 'Z)) Prelude.== 2)
  ]
