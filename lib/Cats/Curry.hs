-- | Currying and uncurrying functors between arbitrary categories.
-- 'Curry₂' fixes the first argument; 'Curry₁' and 'Uncurry₁' transform
-- functor tags, while 'Curry₀' and 'Uncurry₀' act on the functor categories.
--
-- These last two functors are adjoint in both directions. Their units and
-- counits are natural isomorphisms with identity components, witnessing
-- the curry/uncurry equivalence. The round trips need not be equal tags:
-- use the transformations from "Cats.Adjoint" to move between them.
-- For example, @unit (type '(Uncurry₀, Curry₀)) f@ maps @f@ to
-- @Uncurry₁ (Curry₁ f)@; @counit (type '(Uncurry₀, Curry₀)) f@ is its inverse.
--
-- All functor instances must obey their laws, and all component families
-- used as arrows must be natural. In particular 'Uncurry₁' uses 'Eval',
-- whose composition law depends on this naturality.
module Cats.Curry where

import Cats.Adjoint
import Cats.Category
import Cats.CrossProduct
import Cats.Eval
import Cats.Exponential
import Cats.Functor

-- | Fix the first object of a functor on a product category.
type data Curry₂ :: forall a b c. ((a × b) --> c) -> NamesOf a -> (b --> c)

type instance Act (Curry₂ f x) y = Act f '(x, y)

instance
  (Category a, Category b, Functor f, x ∈ a) =>
  Functor (Curry₂ @a @b f x)
  where
  map _ byz = map f (identity x :×: byz)

-- | Turn a binary functor into a functor taking values in a functor category.
type data Curry₁ :: forall a b c. ((a × b) --> c) -> (a --> (c ^ b))

type instance Act (Curry₁ f) x = Curry₂ f x

instance
  (Category a, Category b, Category c, Functor f) =>
  Functor (Curry₁ @a @b @c f)
  where
  map _ axy = EXP \(type i) ->
    map f (axy :×: identity i)

-- | Curry functors and natural transformations. A component at @(x, y)@
-- becomes an outer component at @x@ and an inner component at @y@.
type data Curry₀ :: forall a b c. (c ^ (a × b)) --> ((c ^ b) ^ a)

type instance Act Curry₀ f = Curry₁ f

instance
  (Category a, Category b, Category c) =>
  Functor (Curry₀ @a @b @c)
  where
  map _ (EXP t) = EXP \(type i) -> EXP \(type j) -> t (i, j)

-- | Uncurry a functor valued in a functor category. Its action on objects
-- is @Act (Uncurry₁ f) '(x, y) = Act (Act f x) y@.
type data Uncurry₁ :: forall a b c. (a --> (c ^ b)) -> ((a × b) --> c)

type instance Act (Uncurry₁ f) xy = Act (Act f (Fst xy)) (Snd xy)

instance (Category a, Category b, Category c, Functor f) => Functor (Uncurry₁ @a @b @c f) where
  map @xy @zw _ (l :×: r) =
    with @(Acts f (Fst xy), Acts f (Fst zw)) do
      map (Eval @b @c) (map f l :×: r)

-- | Uncurry functors and natural transformations by evaluating both indices.
type data Uncurry₀ :: forall a b c. ((c ^ b) ^ a) --> (c ^ (a × b))

type instance Act Uncurry₀ f = Uncurry₁ f

instance (Category a, Category b, Category c) => Functor (Uncurry₀ @a @b @c) where
  map _ t = EXP \(type xy) -> (t $$ Fst xy) $$ Snd xy

-- | Currying and uncurrying transpose natural transformations componentwise.
instance (Category a, Category b, Category c) => Curry₀ @a @b @c ⊣ Uncurry₀ @a @b @c where
  leftToRight _ _ t = EXP \(type xy) -> (t $$ Fst xy) $$ Snd xy
  rightToLeft _ _ t = EXP \(type x) -> EXP \(type y) -> t $$ (x, y)

-- | The inverse adjunction supplies the inverse unit and counit maps.
instance (Category a, Category b, Category c) => Uncurry₀ @a @b @c ⊣ Curry₀ @a @b @c where
  leftToRight _ _ t = EXP \(type x) -> EXP \(type y) -> t $$ (x, y)
  rightToLeft _ _ t = EXP \(type xy) -> (t $$ Fst xy) $$ Snd xy
