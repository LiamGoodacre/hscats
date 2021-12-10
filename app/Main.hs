{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Kind
import Data.Proxy
import Prelude (IO, id, putStrLn, (.))

data Dict c where Dict :: c => Dict c

type CAT :: Type -> Type
type CAT i = i -> i -> Type

type FUNCTOR :: forall i j. CAT i -> CAT j -> Type
type FUNCTOR d c = Proxy d -> Proxy c -> Type

type DOM :: forall i (d :: CAT i) c. FUNCTOR d c -> CAT i
type DOM (f :: FUNCTOR d c) = d

type COD :: forall j d (c :: CAT j). FUNCTOR d c -> CAT j
type COD (f :: FUNCTOR d c) = c

type Obj :: forall i. CAT i -> i -> Constraint
type family Obj c x = o | o -> c x

type Cat :: CAT i -> Constraint
class Cat k where
  identity :: Obj k i => k i i
  (∘) :: (Obj k a, Obj k b, Obj k x) => k a b -> k x a -> k x b

type Act :: FUNCTOR (d :: CAT i) (c :: CAT j) -> i -> j
type family Act f o

type Functor :: FUNCTOR d c -> Constraint
class (Cat (DOM f), Cat (COD f)) => Functor f where
  obj_ ::
    Dict (Obj (DOM f) a) ->
    Dict (Obj (COD f) (Act f a))
  mapped_ ::
    ( Obj (DOM f) a,
      Obj (DOM f) b
    ) =>
    DOM f a b ->
    ( ( Obj (COD f) (Act f a),
        Obj (COD f) (Act f b)
      ) =>
      COD f (Act f a) (Act f b) ->
      r
    ) ->
    r

obj ::
  forall f a.
  Functor f =>
  Dict (Obj (DOM f) a) ->
  Dict (Obj (COD f) (Act f a))
obj = obj_ @_ @_ @f

mapped ::
  forall f a b r.
  ( Functor f,
    Obj (DOM f) a,
    Obj (DOM f) b
  ) =>
  DOM f a b ->
  ( ( Obj (COD f) (Act f a),
      Obj (COD f) (Act f b)
    ) =>
    COD f (Act f a) (Act f b) ->
    r
  ) ->
  r
mapped = mapped_ @_ @_ @f

map ::
  forall f a b.
  ( Functor f,
    Obj (DOM f) a,
    Obj (DOM f) b
  ) =>
  DOM f a b ->
  COD f (Act f a) (Act f b)
map d = mapped @f d id

type TYPE :: CAT Type
type TYPE = (->)

type instance Obj TYPE t = (t ~ t, TYPE ~ TYPE)

instance Cat TYPE where
  identity = id
  (∘) = (.)

data READER :: Type -> FUNCTOR TYPE TYPE

type instance Act (READER x) y = x -> y

instance Functor (READER x) where
  obj_ Dict = Dict
  mapped_ f r =
    case obj @(READER x) Dict of
      Dict -> r \g -> f . g

data (∘∘) :: FUNCTOR a b -> FUNCTOR x a -> FUNCTOR x b

type instance Act (f ∘∘ g) x = Act f (Act g x)

instance (Functor f, Functor g) => Functor (f ∘∘ g) where
  obj_ = obj @f . obj @g
  mapped_ dd r = mapped @g dd \gg -> mapped @f gg r

eg0 :: () -> () -> ()
eg0 _ _ = ()

eg1 :: () -> () -> ()
eg1 = map @(READER () ∘∘ READER ()) (\() -> ()) eg0

main :: IO ()
main = putStrLn "main"
