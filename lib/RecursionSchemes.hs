module RecursionSchemes where

import Cats
import Data.Kind (Constraint, Type)
import Data.Type.Equality (type (~))
import Prelude qualified

type data AsFunctor :: forall k. (NamesOf k -> Type) -> (k --> Types)

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
class (c (Fixed k f)) => WithFixed k c (f :: k --> k)

instance (c (Fixed k f)) => WithFixed k c (f :: k --> k)

type HasFixed :: CATEGORY i -> Constraint
class
  ( forall f. (Functor f) => WithFixed k Corecursive f,
    forall f. (Functor f) => WithFixed k Recursive f
  ) =>
  HasFixed k
  where
  type Fixed k (f :: (k --> k)) :: OBJECT k

ana ::
  forall {c} (t :: OBJECT c) a.
  (Corecursive t, a ∈ c) =>
  c a (Act (Base t) a) ->
  c a (ObjectName t)
ana ata = go where go = embed @t ∘ map (Base t) go ∘ ata

cata ::
  forall {c} (t :: OBJECT c) a.
  (Recursive t, a ∈ c) =>
  c (Act (Base t) a) a ->
  c (ObjectName t) a
cata taa = go where go = taa ∘ map (Base t) go ∘ project @t

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
  map _ _ Nil = Nil
  map _ f (Cons x l) = Cons x (f l)

instance Corecursive (AnObject Types [x]) where
  embed_ = \case
    Nil -> []
    Cons x xs -> x : xs

instance Recursive (AnObject Types [x]) where
  project_ = \case
    [] -> Nil
    (x : xs) -> Cons x xs

{- Fix in Types -}

newtype Fix f = In {out :: Act f (Fix f)}

data FixOf :: (Types --> Types) -> OBJECT Types

type instance ObjectName (FixOf f) = Fix f

type instance Base (FixOf f) = f

instance (Functor f) => Corecursive (FixOf f) where
  embed_ = In

instance (Functor f) => Recursive (FixOf f) where
  project_ = out

instance HasFixed Types where
  type Fixed Types f = FixOf f

{- examples -}

_abc :: [Prelude.Int]
_abc =
  refix
    @(AnObject Types [Prelude.Int])
    @(AnObject Types [Prelude.Int])
    [1, 2, 3]

_def :: Fix (AsFunctor @Types (ListF Prelude.Int))
_def =
  refix
    @(AnObject Types [Prelude.Int])
    @(FixOf (AsFunctor (ListF Prelude.Int)))
    _abc

{- Fix in Types^k -}

{-

type FixTT :: forall k . ((Types ^ k) --> (Types ^ k)) -> NamesOf k -> Type
data FixTT f a = InTT {outTT :: Act (Act f (AsFunctor (FixTT f))) a}

instance (Category k, Functor f) => Functor (AsFunctor @k (FixTT @k f)) where
  map _ ab = InTT ∘ map (Act f (AsFunctor (FixTT f))) ab ∘ outTT

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

refold ::
  forall {k} (t :: k --> k) a b .
  (Functor t, a ∈ k, b ∈ k) =>
  k (Act t b) b ->
  k a (Act t a) ->
  k a b
refold f g = f ∘ map @t (refold @t f g) ∘ g

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

-}

{- polymorphically recursive type -}

type data List :: Types --> Types

type instance Act List t = [t]

instance Functor List where
  map _ = Prelude.fmap

{-

data Nested a = a :<: (Nested [a]) | Epsilon
infixr 5 :<:

nested :: Nested Prelude.Int
nested = 1 :<: [2,3,4] :<: [[5,6],[7],[8,9]] :<: Epsilon

nestedLength :: Nested a -> Prelude.Int
nestedLength Epsilon = 0
nestedLength (_ :<: xs) = 1 Prelude.+ nestedLength xs

type NestedF :: forall k . NamesOf k -> ((Types ^ k) --> Types) -> (k --> Types) -> Type
data NestedF a rec f = Act f a :<<: Act rec (List ∘ f) | EpsilonF

data NestedF0 :: forall k . NamesOf k -> ((Types ^ k) --> Types) -> (Types ^ k) --> Types

type instance Act (NestedF0 a rec) f = NestedF a rec f

instance (a ∈ k, Category k, Functor rec) => Functor (NestedF0 @k a rec) where
  map_ ::
    forall f g .
    (f ∈ (Types ^ k), g ∈ (Types ^ k)) =>
    (f ~> g) ->
    NestedF a rec f -> NestedF a rec g
  map_ fg = \case
    EpsilonF -> EpsilonF
    x :<<: xs -> runExp @a fg x :<<:
      map
        @rec
        @(List ∘ f)
        @(List ∘ g)
        (EXP \(Proxy @i) -> map @List (runExp @i fg))
        xs

data NestedF1 :: forall k . NamesOf k -> (Types ^ (Types ^ k)) --> (Types ^ (Types ^ k))

type instance Act (NestedF1 a) rec = NestedF0 a rec

instance (a ∈ k, Category k) => Functor (NestedF1 @k a) where
  map_ st = EXP \(Proxy @i) -> \case
    EpsilonF -> EpsilonF
    x :<<: xs -> x :<<: runExp @(List ∘ i) st xs

-- convert :: Nested a -> FixTT (NestedF1 a) Id
-- convert = _

-}
