-- | Products of categories and functors. 'Fst' and 'Snd' project object
-- names; 'FstFunctor' and 'SndFunctor' also project arrows.
module Cats.CrossProduct where

import Cats.Category
import Cats.Functor
import Data.Type.Equality (type (~))

infixr 7 ×, :×:

data (×) :: CATEGORY s -> CATEGORY t -> CATEGORY (s, t) where
  (:×:) :: l a b -> r x y -> (l × r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type instance Obj (l × r) v = (v ~ '(Fst v, Snd v), Fst v ∈ l, Snd v ∈ r)

instance (Semigroupoid l, Semigroupoid r) => Semigroupoid (l × r) where
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

instance (Category l, Category r) => Category (l × r) where
  identity (a, b) = identity a :×: identity b

infixr 3 ***, &&&

-- | Parallel product: apply a functor to each component independently.
-- @f *** g *** h@ means @f *** (g *** h)@, with a right-nested product
-- category as its source and target.
type data (***) :: (a --> s) -> (b --> t) -> ((a × b) --> (s × t))

type instance Act (f *** g) o = '(Act f (Fst o), Act g (Snd o))

instance (Functor f, Functor g) => Functor (f *** g) where
  map _ (l :×: r) = map f l :×: map g r

-- | Pointwise product: apply both functors to the same object and arrow.
-- @f &&& g &&& h@ means @f &&& (g &&& h)@. This pairs functors into a
-- product category; it does not construct a product inside their codomains.
type data (&&&) :: (d --> l) -> (d --> r) -> (d --> (l × r))

type instance Act (f &&& g) o = '(Act f o, Act g o)

instance (Functor f, Functor g) => Functor (f &&& g) where
  map _ t = map f t :×: map g t

-- | Project the left object and arrow of a product category.
type data FstFunctor :: forall a b. (a × b) --> a

type instance Act FstFunctor ab = Fst ab

instance (Category a, Category b) => Functor (FstFunctor @a @b) where
  map _ (l :×: _) = l

-- | Project the right object and arrow of a product category.
type data SndFunctor :: forall a b. (a × b) --> b

type instance Act SndFunctor ab = Snd ab

instance (Category a, Category b) => Functor (SndFunctor @a @b) where
  map _ (_ :×: r) = r
