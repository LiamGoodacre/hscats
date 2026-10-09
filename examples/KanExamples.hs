-- | Experimental existential encoding of right Kan extensions into Types.
-- This module is compiled and exercised by the hscats-examples target.
module KanExamples where

import Cats
import Data.Kind (Type)
import Data.Proxy (Proxy (..))
import Prelude qualified

-- (• g) ⊣ (/ g)
-- aka (PostCompose g ⊣ PostRan g)

type data PostCompose :: (c --> c') -> (a ^ c') --> (a ^ c)

type instance Act (PostCompose g) f = f • g

instance
  (Category c, Category c', Category a, Functor g) =>
  Functor (PostCompose @c @c' @a g)
  where
  map _ = above

type Ran :: (x --> Types) -> (x --> z) -> NamesOf z -> Type
data Ran h g a where
  RAN ::
    (Functor f) =>
    Proxy f ->
    ((f • g) ~> h) ->
    Act f a ->
    Ran h g a

-- NOTE: currently y is always Types
type data (/) :: (x --> y) -> (x --> z) -> (z --> y)

type instance Act (h / g) o = Ran h g o

instance (Category x, Category z) => Functor ((/) @x @Types @z h g) where
  map _ zab (RAN (Proxy @f) fgh fa) =
    RAN (Proxy @f) fgh (map f zab fa)

-- NOTE: currently y is always Types
type data PostRan :: (x --> z) -> (y ^ x) --> (y ^ z)

type instance Act (PostRan g) h = h / g

instance
  (Category x, Category z, Functor g) =>
  Functor (PostRan @x @z @Types g)
  where
  map _ ab =
    EXP \_ (RAN p fga fi) ->
      RAN p (ab ∘ fga) fi

instance (Functor g) => PostCompose g ⊣ PostRan @x @z @Types g where
  rightToLeft _ _ a_bg =
    EXP \(type i) ag ->
      case (a_bg $$ Act g i) ag of
        RAN _ fg_b fgi ->
          (fg_b $$ i) fgi

  leftToRight _ _ ag_b =
    EXP \_ -> RAN Proxy ag_b

type Codensity :: (x --> Types) -> (Types --> Types)
type Codensity f = f / f

-- Along the identity functor, the existential can be evaluated directly.
lowerRanId :: forall (h :: Types --> Types) a. Ran h Id a -> Act h a
lowerRanId (RAN _ transform value) = (transform $$ a) value

type Lists = Constructor []

sample :: Ran Lists Id Prelude.Int
sample = RAN (Proxy @Lists) (EXP \_ -> Prelude.id) [1, 2, 3]

first :: Lists ~> Constructor Prelude.Maybe
first = EXP \_ -> \case
  [] -> Prelude.Nothing
  x : _ -> Prelude.Just x

checks :: [(Prelude.String, Prelude.Bool)]
checks =
  [ ("Right Kan extension along Id evaluates", lowerRanId sample Prelude.== [1, 2, 3]),
    ("Right Kan mapping changes the result type", lowerRanId (map (Lists / Id) Prelude.show sample) Prelude.== ["1", "2", "3"]),
    ("PostRan maps a natural transformation", lowerRanId ((map (PostRan Id) first $$ Prelude.Int) sample) Prelude.== Prelude.Just 1),
    ("Right Kan adjunction unit retains data", lowerRanId ((unit (type '(PostRan Id, PostCompose Id)) Lists $$ Prelude.Int) [1, 2, 3]) Prelude.== [1, 2, 3]),
    ("Right Kan adjunction counit evaluates", (counit (type '(PostCompose Id, PostRan Id)) Lists $$ Prelude.Int) sample Prelude.== [1, 2, 3])
  ]
