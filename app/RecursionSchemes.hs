{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module RecursionSchemes where

import Data.Kind
import Defs
import Prelude qualified

data AsFunctor :: forall k. (NamesOf k -> Type) -> (k --> Types)

type instance Act (AsFunctor f) x = f x

{- fixed point functors -}

type Base :: forall k. NamesOf k -> k --> k
type family Base t

class Functor (Base @k t) => Corecursive k t where
  embed_ :: t ∈ k => k (Act (Base @k t) t) t

embed :: forall {k} t. (Corecursive k t, t ∈ k) => k (Act (Base @k t) t) t
embed = embed_

class Functor (Base @k t) => Recursive k t where
  project_ :: t ∈ k => k t (Act (Base @k t) t)

project :: forall {k} t. (Recursive k t, t ∈ k) => k t (Act (Base @k t) t)
project = project_

ana ::
  forall {k} t a.
  (Corecursive k t, t ∈ k, a ∈ k) =>
  k a (Act (Base @k t) a) ->
  k a t
ana t = go where go = embed @t ∘ map @(Base @k t) go ∘ t

cata ::
  forall {k} t a.
  (Recursive k t, t ∈ k, a ∈ k) =>
  k (Act (Base @k t) a) a ->
  k t a
cata t = go where go = t ∘ map @(Base @k t) go ∘ project @t

refix ::
  ( Recursive Types s,
    Corecursive Types t,
    Base @Types s ~ Base @Types t
  ) =>
  s ->
  t
refix = cata embed

-- fix example with lists

data ListF x l = Nil | Cons x l

type instance Base @Types [x] = AsFunctor (ListF x)

instance Corecursive Types [x] where
  embed_ = \case
    Nil -> []
    Cons x xs -> x : xs

instance Recursive Types [x] where
  project_ = \case
    [] -> Nil
    (x : xs) -> Cons x xs

instance Functor (AsFunctor @Types (ListF x)) where
  map_ _ Nil = Nil
  map_ f (Cons x l) = Cons x (f l)

abc :: [Prelude.Int]
abc = refix [1, 2, 3]

-- fix fix

newtype Fix (f :: Types --> Types) = In {out :: Act f (Fix f)}

type instance Base @Types (Fix f) = f

instance Functor f => Corecursive Types (Fix f) where
  embed_ = In

instance Functor f => Recursive Types (Fix f) where
  project_ = out

def :: Fix (AsFunctor (ListF Prelude.Int))
def = refix abc
