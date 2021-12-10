{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# OPTIONS_GHC -Wall -Werror -Wextra #-}

module Main where

import Data.Kind
import Data.Proxy
import Prelude
  ( Either (..),
    IO,
    Monoid (..),
    Semigroup ((<>)),
    either,
    fst,
    id,
    putStrLn,
    snd,
    (.),
  )

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

class (Obj (COD f) (Act f o)) => Acts f o

instance (Obj (COD f) (Act f o)) => Acts f o

type Functorial :: FUNCTOR (d :: CAT o) c -> o -> Constraint
type Functorial f o = (Obj (DOM f) o => Acts f o)

type Functor :: FUNCTOR d c -> Constraint
class (Cat (DOM f), Cat (COD f), forall o. Functorial f o) => Functor f where
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

data MONOID :: Type -> CAT () where
  MONOID :: m -> MONOID m '() '()

type instance Obj (MONOID m) x = (x ~ '(), MONOID m ~ MONOID m)

instance Monoid m => Cat (MONOID m) where
  identity = MONOID mempty
  MONOID l ∘ MONOID r = MONOID (l <> r)

data (××) :: CAT s -> CAT t -> CAT (s, t) where
  (:××:) :: l a b -> r x y -> (l ×× r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type instance
  Obj (l ×× r) v =
    ( v ~ '(Fst v, Snd v),
      Obj l (Fst v),
      Obj r (Snd v),
      (l ×× r) ~ (l ×× r)
    )

instance (Cat l, Cat r) => Cat (l ×× r) where
  identity = identity :××: identity
  (a :××: b) ∘ (c :××: d) = (a ∘ c) :××: (b ∘ d)

data DELTA :: FUNCTOR k (k ×× k)

type instance Act DELTA x = '(x, x)

instance Cat k => Functor (DELTA :: FUNCTOR k (k ×× k)) where
  obj_ Dict = Dict
  mapped_ f r = r (f :××: f)

data (∧) :: FUNCTOR (TYPE ×× TYPE) TYPE

type instance Act (∧) x = (Fst x, Snd x)

instance Functor (∧) where
  obj_ Dict = Dict
  mapped_ (f :××: g) r = r \(a, b) -> (f a, g b)

data (∨) :: FUNCTOR (TYPE ×× TYPE) TYPE

type instance Act (∨) x = Either (Fst x) (Snd x)

instance Functor (∨) where
  obj_ Dict = Dict
  mapped_ (f :××: g) r = r \case
    Left a -> Left (f a)
    Right b -> Right (g b)

type Adjoint :: FUNCTOR c d -> FUNCTOR d c -> Constraint
class (Functor f, Functor g) => Adjoint f (g :: FUNCTOR d c) where
  leftAdjointed_ ::
    forall a b.
    ( Obj c a,
      Obj d b
    ) =>
    c a (Act g b) ->
    d (Act f a) b

  rightAdjointed_ ::
    forall a b.
    ( Obj c a,
      Obj d b
    ) =>
    d (Act f a) b ->
    c a (Act g b)

leftAdjointed ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
    Obj c a,
    Obj d b
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjointed = leftAdjointed_ @c @d @f @g

rightAdjointed ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
    Obj c a,
    Obj d b
  ) =>
  d (Act f a) b ->
  c a (Act g b)
rightAdjointed = rightAdjointed_ @c @d @f @g

instance Adjoint DELTA (∧) where
  leftAdjointed_ t = (fst . t) :××: (snd . t)
  rightAdjointed_ (f :××: g) = \x -> (f x, g x)

instance Adjoint (∨) DELTA where
  leftAdjointed_ (f :××: g) = f `either` g
  rightAdjointed_ t = (t . Left) :××: (t . Right)

type MONAD :: CAT i -> Type
type MONAD k = FUNCTOR k k

type COMONAD :: CAT i -> Type
type COMONAD k = FUNCTOR k k

unit ::
  forall
    {c}
    {d}
    (m :: MONAD c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘∘ f),
    Adjoint f g,
    Obj c a
  ) =>
  c a (Act m a)
unit = rightAdjointed @f @g identity

counit ::
  forall
    {c}
    {d}
    (w :: COMONAD d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘∘ g),
    Adjoint f g,
    Obj d a
  ) =>
  d (Act w a) a
counit = leftAdjointed @f @g identity

join ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (m :: MONAD c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘∘ f),
    Adjoint f g,
    Obj c a
  ) =>
  c (Act (m ∘∘ m) a) (Act m a)
join = do
  let t :: d (Act f (Act g (Act f a))) (Act f a)
      t = counit @(f ∘∘ g)
  map @g t

extend ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (w :: COMONAD d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘∘ g),
    Adjoint f g,
    Obj d a
  ) =>
  d (Act w a) (Act (w ∘∘ w) a)
extend = do
  let t :: c (Act g a) (Act g (Act f (Act g a)))
      t = unit @(g ∘∘ f)
  map @f t

main :: IO ()
main = putStrLn "main"
