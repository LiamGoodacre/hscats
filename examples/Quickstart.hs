{-# LANGUAGE GHC2024 #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE QualifiedDo #-}
{-# LANGUAGE RequiredTypeArguments #-}
{-# LANGUAGE TypeAbstractions #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Quickstart where

import Cats
import Cats.Applicative qualified as A
import Cats.Do qualified as Do
import Cats.Monad qualified as M
import Prelude qualified as P

type data Optional :: Types --> Types

type instance Act Optional a = P.Maybe a

instance Functor Optional where
  map _ = P.fmap

inject :: Id ~> Optional
inject = EXP \_ -> P.Just

describe :: P.Int -> P.Maybe P.String
describe = map Optional P.show ∘ (inject $$ P.Int)

choices :: [P.Int]
choices = Do.with (type (TypeConstructor [])) Do.do
  x <- [1, 2]
  Do.pure (x P.+ 10)

-- The first stored component runs after the second. Bool is hidden inside.
parity :: DataProcompose (Hom Types) (Hom Types) P.Int P.String
parity = MkProcompose @P.Bool (\b -> if b then "even" else "odd") P.even

runParity :: P.Int -> P.String
runParity n = case parity of
  MkProcompose outer inner -> outer (inner n)

main :: P.IO ()
main = do
  P.print (describe 7)
  P.print (A.liftA2 (type (TypeConstructor [])) (P.+) [1, 2 :: P.Int] [10, 20])
  P.print (M.flatMap (type (TypeConstructor [])) (\n -> [n, n P.+ 10]) [1, 2 :: P.Int])
  P.print choices
  P.print (runParity 4)
