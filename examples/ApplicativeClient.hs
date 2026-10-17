{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

-- A client implements the operation classes; the constraint class is derived.
module ApplicativeClient (example) where

import Cats
import Cats.Applicative (Applicative, Lift0 (lift0), Lift2 (lift2), liftA2)
import Prelude qualified as P

type data Optional :: Types --> Types

type instance Act Optional a = P.Maybe a

instance Functor Optional where
  map _ = P.fmap

instance Lift0 (∧) Optional where
  lift0 _ _ = EXP \_ -> P.Just

instance Lift2 (∧) Optional where
  lift2 = EXP \_ (DataDayTypes k left right) -> P.liftA2 (P.curry k) left right

pair ::
  forall (f :: Types --> Types) ->
  (Applicative f) => Act f P.Int -> Act f P.Bool -> Act f (P.Int, P.Bool)
pair f = liftA2 @P.Int @P.Bool @(P.Int, P.Bool) f (,)

example :: P.Maybe (P.Int, P.Bool)
example = pair Optional (P.Just 7) (P.Just P.True)
