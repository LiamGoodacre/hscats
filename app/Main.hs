{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RebindableSyntax #-}
{-# LANGUAGE RecordWildCards #-}
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
    Int,
    Monoid (..),
    Num (..),
    Semigroup ((<>)),
    either,
    fromInteger,
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

type ENDO :: CAT i -> Type
type ENDO k = FUNCTOR k k

type DOM :: forall i (d :: CAT i) c. FUNCTOR d c -> CAT i
type DOM (f :: FUNCTOR d c) = d

type COD :: forall j d (c :: CAT j). FUNCTOR d c -> CAT j
type COD (f :: FUNCTOR d c) = c

type (∈) :: forall i. i -> CAT i -> Constraint
type family x ∈ k = o | o -> k x

type Cat :: CAT i -> Constraint
class Cat k where
  identity :: i ∈ k => k i i
  (∘) :: (a ∈ k, b ∈ k, x ∈ k) => k a b -> k x a -> k x b

type Act :: FUNCTOR (d :: CAT i) (c :: CAT j) -> i -> j
type family Act f o

class (Act f o ∈ COD f) => Acts f o

instance (Act f o ∈ COD f) => Acts f o

type Functorial :: FUNCTOR (d :: CAT o) c -> o -> Constraint
type Functorial f o = (o ∈ DOM f => Acts f o)

type Functor :: FUNCTOR d c -> Constraint
class (Cat (DOM f), Cat (COD f), forall o. Functorial f o) => Functor f where
  map_ ::
    ( a ∈ DOM f,
      b ∈ DOM f
    ) =>
    DOM f a b ->
    COD f (Act f a) (Act f b)

map ::
  forall f a b.
  ( Functor f,
    a ∈ DOM f,
    b ∈ DOM f
  ) =>
  DOM f a b ->
  COD f (Act f a) (Act f b)
map d = map_ @_ @_ @f d


data Id :: FUNCTOR i i
type instance Act Id x = x
instance Cat i => Functor (Id :: FUNCTOR i i) where
  map_ = id

data (∘) :: FUNCTOR a b -> FUNCTOR x a -> FUNCTOR x b
type instance Act (f ∘ g) x = Act f (Act g x)
instance (Functor f, Functor g) => Functor (f ∘ g) where
  map_ = map @f . map @g

data (×) :: CAT s -> CAT t -> CAT (s, t) where
  (:×:) :: l a b -> r x y -> (l × r) '(a, x) '(b, y)

type Fst :: (l, r) -> l
type family Fst p where
  Fst '(a, b) = a

type Snd :: (l, r) -> r
type family Snd p where
  Snd '(a, b) = b

type instance
  v ∈ (l × r) =
    ( v ~ '(Fst v, Snd v),
      Fst v ∈ l,
      Snd v ∈ r,
      (l × r) ~ (l × r)
    )

instance (Cat l, Cat r) => Cat (l × r) where
  identity = identity :×: identity
  (a :×: b) ∘ (c :×: d) = (a ∘ c) :×: (b ∘ d)

data OP :: CAT i -> CAT i where OP :: k b a -> OP k a b
type instance i ∈ OP k = (i ∈ k, OP k ~ OP k)
instance Cat k => Cat (OP k) where
  identity = OP identity
  OP g ∘ OP f = OP (f ∘ g)

type TYPE = (->) :: CAT Type
type instance t ∈ TYPE = (t ~ t, TYPE ~ TYPE)
instance Cat TYPE where
  identity = id
  (∘) = (.)

-- yoneda embeddings

data Y :: forall (k :: CAT i) -> i -> FUNCTOR k TYPE
type instance Act (Y k d) c = k d c
instance (d ∈ k, Cat k) => Functor (Y k d) where
  map_ = (∘)

data K :: forall (k :: CAT i) -> i -> FUNCTOR (OP k) TYPE
type instance Act (K k c) d = k d c
instance (d ∈ k, Cat k) => Functor (K k d) where
  map_ (OP g) f = f ∘ g

data HOM :: forall (k :: CAT i) -> FUNCTOR (OP k × k) TYPE
type instance Act (HOM k) o = k (Fst o) (Snd o)
-- uncomment for panic - https://gitlab.haskell.org/ghc/ghc/-/issues/20231
-- instance Cat k => Functor (HOM k) where
--   map_ (f :×: g) t = f ∘ t ∘ g

type Adjoint :: FUNCTOR c d -> FUNCTOR d c -> Constraint
class (Functor f, Functor g) => Adjoint f (g :: FUNCTOR d c) where
  leftAdjoint_ ::
    forall a b.
    ( a ∈ c,
      b ∈ d
    ) =>
    c a (Act g b) ->
    d (Act f a) b

  rightAdjoint_ ::
    forall a b.
    ( a ∈ c,
      b ∈ d
    ) =>
    d (Act f a) b ->
    c a (Act g b)

leftAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
    a ∈ c,
    b ∈ d
  ) =>
  c a (Act g b) ->
  d (Act f a) b
leftAdjoint = leftAdjoint_ @c @d @f @g

rightAdjoint ::
  forall {c} {d} (f :: FUNCTOR c d) (g :: FUNCTOR d c) a b.
  ( Adjoint f g,
    a ∈ c,
    b ∈ d
  ) =>
  d (Act f a) b ->
  c a (Act g b)
rightAdjoint = rightAdjoint_ @c @d @f @g

unit ::
  forall
    {c}
    {d}
    (m :: ENDO c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘ f),
    Adjoint f g,
    a ∈ c
  ) =>
  c a (Act m a)
unit = rightAdjoint @f @g identity

counit ::
  forall
    {c}
    {d}
    (w :: ENDO d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘ g),
    Adjoint f g,
    a ∈ d
  ) =>
  d (Act w a) a
counit = leftAdjoint @f @g identity

join ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (m :: ENDO c)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( m ~ (g ∘ f),
    Adjoint f g,
    a ∈ c
  ) =>
  c (Act (m ∘ m) a) (Act m a)
join = do
  let t :: d (Act f (Act g (Act f a))) (Act f a)
      t = counit @(f ∘ g)
  map @g t

extend ::
  forall
    {i}
    {c :: CAT i}
    {d :: CAT i}
    (w :: ENDO d)
    {f :: FUNCTOR c d}
    {g :: FUNCTOR d c}
    a.
  ( w ~ (f ∘ g),
    Adjoint f g,
    a ∈ d
  ) =>
  d (Act w a) (Act (w ∘ w) a)
extend = do
  let t :: c (Act g a) (Act g (Act f (Act g a)))
      t = unit @(g ∘ f)
  map @f t

---


data READER :: Type -> FUNCTOR TYPE TYPE
type instance Act (READER x) y = x -> y
instance Functor (READER x) where
  map_ = (.)


data ENV :: Type -> FUNCTOR TYPE TYPE
type instance Act (ENV x) y = (x, y)
instance Functor (ENV x) where
  map_ f (l, r) = (l, f r)


data MONOID :: Type -> CAT () where
  MONOID :: m -> MONOID m '() '()

type instance x ∈ MONOID m =
  ( x ~ '(),
    MONOID m ~ MONOID m
  )

instance Monoid m => Cat (MONOID m) where
  identity = MONOID mempty
  MONOID l ∘ MONOID r = MONOID (l <> r)



data DELTA :: forall (k :: CAT i) -> FUNCTOR k (k × k)
type instance Act (DELTA k) x = '(x, x)
instance Cat k => Functor (DELTA k) where
  map_ f = (f :×: f)


data (∧) :: FUNCTOR (TYPE × TYPE) TYPE
type instance Act (∧) x = (Fst x, Snd x)
instance Functor (∧) where
  map_ (f :×: g) (a, b) = (f a, g b)


data (∨) :: FUNCTOR (TYPE × TYPE) TYPE
type instance Act (∨) x = Either (Fst x) (Snd x)
instance Functor (∨) where
  map_ (f :×: g) = \case
    Left a -> Left (f a)
    Right b -> Right (g b)


instance Adjoint (DELTA TYPE) (∧) where
  leftAdjoint_ t = (fst . t) :×: (snd . t)
  rightAdjoint_ (f :×: g) = \x -> (f x, g x)

instance Adjoint (∨) (DELTA TYPE) where
  leftAdjoint_ (f :×: g) = f `either` g
  rightAdjoint_ t = (t . Left) :×: (t . Right)

stateFlatMap ::
  forall s a b.
  Act (STATE s) a ->
  (a -> Act (STATE s) b) ->
  Act (STATE s) b
stateFlatMap m f = join @(STATE s) (map @(STATE s) f m)

type STATE s = READER s ∘ ENV s

instance Adjoint (ENV s) (READER s) where
  leftAdjoint_ asb (s, a) = asb a s
  rightAdjoint_ sab a s = sab (s, a)

get :: Act (STATE s) s
get s = (s, s)

put :: s -> Act (STATE s) ()
put v _ = (v, ())

modify :: (s -> s) -> Act (STATE s) ()
modify t s = (t s, ())

data Do m = Do
  (forall a b. Act m a -> (a -> Act m b) -> Act m b)
  (forall a. a -> Act m a)

(>>=) :: forall m a b. (?monad :: Do m) => Act m a -> (a -> Act m b) -> Act m b
(>>=) = let Do f _ =  ?monad in f @a @b

pure :: forall m a. (?monad :: Do m) => a -> Act m a
pure = let Do _ u = ?monad in u

stateMonad :: ((?monad :: Do (STATE s)) => r) -> r
stateMonad t = let ?monad = Do stateFlatMap (unit @(STATE _)) in t

postinc :: Act (STATE Int) Int
postinc = stateMonad do
  x <- get
  _ <- put (x + 1)
  pure x

-- f ∘ g ~> h
-- f ~> h / g
data (//) :: FUNCTOR d c -> FUNCTOR d d -> FUNCTOR c d
-- TODO - make more general
newtype Ran h g a = Ran (forall i . (a -> Act g i) -> Act h i)
type instance Act (h // g) x = Ran h g x

type CODENSITY f = f // f

-- f ~> g ∘ h
-- f \\ h ~> g
data (\\) :: FUNCTOR d c -> FUNCTOR d d -> FUNCTOR c d
-- TODO - make more general
data Lan f h a where
  (:\\:) :: Act f b -> (Act h b -> a) -> Lan f h a

main :: IO ()
main = putStrLn "main"
