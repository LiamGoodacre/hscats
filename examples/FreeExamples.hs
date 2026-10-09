-- | Church-encoded free-monad experiment. Its interpreters are restricted
-- to composites of adjoints through Types; this is not a general free-monad API.
module FreeExamples where

import Cats
import Data.Kind (Type)
import Data.Type.Equality (type (~))
import Prelude qualified

-- Env s ⊣ Reader s

type data Reader :: Type -> (Types --> Types)

type instance Act (Reader x) y = x -> y

instance Functor (Reader x) where
  map _ = (∘)

type data Env :: Type -> (Types --> Types)

type instance Act (Env x) y = (y, x)

instance Functor (Env x) where
  map _ f (l, r) = (f l, r)

instance Env s ⊣ Reader s where
  rightToLeft _ _ = Prelude.uncurry
  leftToRight _ _ = Prelude.curry

newtype NT t m = NT (t ~> m)

type Free :: (Types --> Types) -> Type -> Type
data Free t a = FREE
  { runFree ::
      forall m a' ->
      (AdjunctionMonadBy m Types, a' ~ a) =>
      NT t m ->
      Act m a
  }

type data Free0 :: (k --> k) -> (k --> k)

type data Free1 :: (k ^ k) --> (k ^ k)

type data Free2 :: ((k ^ k) × k) --> k

type instance Act (Free0 f) o = Free f o

type instance Act Free1 f = Free0 f

type instance Act Free2 fx = Free (Fst fx) (Snd fx)

instance Functor (Free0 @Types t) where
  map _ (a_b :: a -> b) r = FREE \m _ t_m -> map m a_b (runFree r m a t_m)

instance Functor (Free1 @Types) where
  map _ a_b = EXP \_ (FREE f) -> FREE \m (type a) (NT t_m) -> f m a (NT (t_m ∘ a_b))

instance Functor (Free2 @Types) where
  map _ (s_t :×: (a_b :: Types a b)) = \(FREE f) ->
    FREE \m _ (NT t_m) ->
      map m a_b (f m a (NT (t_m ∘ s_t)))

liftFree :: forall (t :: Types --> Types) a. Act t a -> Free t a
liftFree value = FREE \_ _ (NT transform) -> (transform $$ a) value

type State = Reader Prelude.Int • Env Prelude.Int

tick :: Id ~> State
tick = EXP \_ x s -> (x, s Prelude.+ 1)

sample :: Free Id Prelude.Int
sample = liftFree @Id 7

checks :: [(Prelude.String, Prelude.Bool)]
checks =
  [ ("Church encoding interprets an operation", runFree sample State Prelude.Int (NT tick) 0 Prelude.== (7, 1)),
    ("Church result mapping retains the effect", runFree (map (Free0 Id) Prelude.show sample) State Prelude.String (NT tick) 0 Prelude.== ("7", 1)),
    ("Church transformation mapping retains the interpreter", runFree ((map Free1 (identity Id) $$ Prelude.Int) sample) State Prelude.Int (NT tick) 0 Prelude.== (7, 1)),
    ("Church evaluation maps both arguments", runFree (map Free2 (identity Id :×: Prelude.show) sample) State Prelude.String (NT tick) 0 Prelude.== ("7", 1))
  ]
