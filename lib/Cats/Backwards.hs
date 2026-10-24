module Cats.Backwards where

import Cats.Applicative
import Cats.Day
import Cats.Exponential
import Cats.Functor
import Cats.Semigroupoid
import Cats.Symmetric

type data Backwards :: forall d c. (d --> c) -> (d --> c)

type instance Act (Backwards f) x = Act f x

instance (Functor f) => Functor (Backwards f) where
  map _ = map f

instance
  ( Symmetric (Day₁ @d @c op),
    Functor f,
    Lift2 op f
  ) =>
  Lift2 op (Backwards @d @c f)
  where
  lift2 _ _ = lift2 _ _ ∘ symm (type (Day₁ @d @c op)) (type _) (type _)

instance (Functor f, Lift0 op f) => Lift0 op (Backwards @d @c f) where
  lift0 _ _ = castExp ∘ lift0 (type op) (type f)
