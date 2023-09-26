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
import Data.Proxy

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

type WithFixed ::
  forall (k :: CATEGORY i) ->
  (OBJECT k -> Constraint) ->
  (k --> k) ->
  Constraint
class c (Fixed k f) => WithFixed k c (f :: k --> k)

instance c (Fixed k f) => WithFixed k c (f :: k --> k)

type HasFixed :: CATEGORY i -> Constraint
class
  ( forall f. Functor f => WithFixed k Corecursive f,
    forall f. Functor f => WithFixed k Recursive f
  ) =>
  HasFixed k
  where
  type Fixed k (f :: (k --> k)) :: OBJECT k

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

instance HasFixed Types where
  type Fixed Types f = FixOf f

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

{- Fix in Types^k -}

type FixTT :: forall k . ((Types ^ k) --> (Types ^ k)) -> NamesOf k -> Type
data FixTT f a = InTT {outTT :: Act (Act f (AsFunctor (FixTT f))) a}

instance (Category k, Functor f) => Functor (AsFunctor @k (FixTT @k f)) where
  map_ ab = InTT ∘ map @(Act f (AsFunctor (FixTT f))) ab ∘ outTT

data FixTTOf :: forall k . ((Types ^ k) --> (Types ^ k)) -> OBJECT (Types ^ k)

type instance ObjectName (FixTTOf @k f) = AsFunctor @k (FixTT @k f)

type instance Base (FixTTOf f) = f

instance (Category k, Functor f) => Corecursive (FixTTOf @k f) where
  embed_ = EXP \_ -> InTT

instance (Category k, Functor f) => Recursive (FixTTOf @k f) where
  project_ = EXP \_ -> outTT

instance Category k => HasFixed (Types ^ k) where
  type Fixed (Types ^ k) f = FixTTOf @k f

hcata ::
  forall h f.
  (Functor h, Functor f) =>
  (Act h f ~> f) ->
  (ObjectName (FixTTOf h) ~> f)
hcata = cata @(FixTTOf h)

{- Demonstrate FixTT with Vectors -}

type VecF :: Type -> ((:~:) @N --> Types) -> N -> Type
data VecF v rec n where
  ConsF :: v -> Act rec n -> VecF v rec ('S n)
  NilF :: VecF v rec 'Z

data VecFunc0 :: Type -> ((:~:) @N --> Types) -> ((:~:) @N --> Types)
type instance Act (VecFunc0 v rec) n = VecF v rec n

instance Functor rec => Functor (VecFunc0 v rec) where
  map_ REFL x = x

data VecFunc1 :: Type -> (Types ^ (:~:) @N) --> (Types ^ (:~:) @N)
type instance Act (VecFunc1 v) rec = VecFunc0 v rec

instance Functor (VecFunc1 v) where
  map_ ::
    (a ∈ (Types ^ (:~:)), b ∈ (Types ^ (:~:))) =>
    (a ~> b) ->
    (Act (VecFunc1 v) a ~> Act (VecFunc1 v) b)
  map_ f = EXP \(Proxy  @hello) -> \case
    NilF -> NilF
    ConsF @_ @_ @n x xs -> ConsF x (runExp @n f xs)

type Vec' a n = FixTT (VecFunc1 a) n

nil :: Vec' a 'Z
nil = InTT NilF

cons :: a -> Vec' a n -> Vec' a ('S n)
cons x xs = InTT (ConsF x xs)

type Plus :: N -> N -> N
type family Plus l r where
  Plus 'Z r = r
  Plus ('S l) r = 'S (Plus l r)

newtype Appended m a n =
  Append { getAppended :: Vec' a m -> Vec' a (Plus n m) }

type Appending m a = AsFunctor @(:~:) (Appended m a)

instance Functor (AsFunctor @(:~:) (Appended m a)) where
  map_ REFL = identity

appendVec :: forall a n m . Vec' a n -> Vec' a m -> Vec' a (Plus n m)
appendVec xs ys = getAppended (runExp (hcata alg) xs) ys where
  alg :: VecFunc0 a (Appending m a) ~> Appending m a
  alg = EXP \_ -> \case
    NilF -> Append identity
    ConsF x rec -> Append \zs -> cons x (getAppended rec zs)

example0 :: Vec' Prelude.Integer ('S ('S ('S 'Z)))
example0 = cons 1 (cons 2 (cons 3 nil))

example1 :: Vec' Prelude.Integer ('S ('S 'Z))
example1 = cons 4 (cons 5 nil)

example2 :: Vec' Prelude.Integer ('S ('S ('S ('S ('S 'Z)))))
example2 = appendVec example0 example1
