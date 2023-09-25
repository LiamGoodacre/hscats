{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module RecursionSchemes where

import Data.Kind
import Defs
import Prelude qualified

data AsFunctor :: forall k. (NamesOf k -> Type) -> (k --> Types)

type instance Act (AsFunctor f) x = f x

{- fixed point functors -}

type Base :: forall c. OBJECT c -> (c --> c)
type family Base t

type Corecursive :: forall c. OBJECT c -> Constraint
class (ObjectName t ∈ c, Functor (Base t)) => Corecursive (t :: OBJECT c) where
  embed_ :: c (Act (Base t) (ObjectName t)) (ObjectName t)

embed ::
  forall {c} (t :: OBJECT c).
  (Corecursive t) =>
  c (Act (Base t) (ObjectName t)) (ObjectName t)
embed = embed_ @_ @t

type Recursive :: forall c. OBJECT c -> Constraint
class (ObjectName t ∈ c, Functor (Base t)) => Recursive (t :: OBJECT c) where
  project_ :: c (ObjectName t) (Act (Base t) (ObjectName t))

project ::
  forall {c} (t :: OBJECT c).
  (Recursive t) =>
  c (ObjectName t) (Act (Base t) (ObjectName t))
project = project_ @_ @t

ana ::
  forall {c} (t :: OBJECT c) a.
  (Corecursive t, a ∈ c) =>
  c a (Act (Base t) a) ->
  c a (ObjectName t)
ana t = go where go = embed @t ∘ map @(Base t) go ∘ t

cata ::
  forall {c} (t :: OBJECT c) a.
  (Recursive t, a ∈ c) =>
  c (Act (Base t) a) a ->
  c (ObjectName t) a
cata t = go where go = t ∘ map @(Base t) go ∘ project @t

refix ::
  forall (s :: OBJECT Types) (t :: OBJECT Types).
  ( Recursive s,
    Corecursive t,
    Base s ~ Base t
  ) =>
  ObjectName s ->
  ObjectName t
refix = cata @s (embed @t)

-- fix example with lists

data ListF x l = Nil | Cons x l

type instance Base (AnObject Types [x]) = AsFunctor (ListF x)

instance Functor (AsFunctor @Types (ListF x)) where
  map_ _ Nil = Nil
  map_ f (Cons x l) = Cons x (f l)

instance Corecursive (AnObject Types [x]) where
  embed_ = \case
    Nil -> []
    Cons x xs -> x : xs

instance Recursive (AnObject Types [x]) where
  project_ = \case
    [] -> Nil
    (x : xs) -> Cons x xs

{- Fix in Types -}

data Fix f = In {out :: Act f (Fix f)}

data FixOf :: (Types --> Types) -> OBJECT Types

type instance ObjectName (FixOf f) = Fix f

type instance Base (FixOf f) = f

instance Functor f => Corecursive (FixOf f) where
  embed_ = In

instance Functor f => Recursive (FixOf f) where
  project_ = out

type IsFixed :: OBJECT k -> Constraint
class (Corecursive f, Recursive f) => IsFixed f

instance Functor f => IsFixed (FixOf f)

{- examples -}

abc :: [Prelude.Int]
abc =
  refix
    @(AnObject Types [Prelude.Int])
    @(AnObject Types [Prelude.Int])
    [1, 2, 3]

def :: Fix (AsFunctor @Types (ListF Prelude.Int))
def =
  refix
    @(AnObject Types [Prelude.Int])
    @(FixOf (AsFunctor (ListF Prelude.Int)))
    abc
