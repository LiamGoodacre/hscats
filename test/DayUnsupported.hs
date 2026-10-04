{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

-- Isolate the intentionally rejected expression so the normal test suite can
-- check this API restriction without invoking a separate compiler process.
module DayUnsupported (check) where

import Cats
import Control.Exception qualified as E
import Data.List qualified as List
import DayChecks
import Prelude qualified as P

unsupportedRoundTrip :: (P.Int, P.Int)
unsupportedRoundTrip =
  observeCounterexample
    ((rassoc CounterexampleDay Unit Unit Unit ∘ lassoc CounterexampleDay Unit Unit Unit $$ ()) counterexample)

-- With the old generic instance this succeeds and returns (5, 0), even though
-- the original is (2, 3). The library must not supply that unlawful instance.
check :: P.IO ()
check = do
  result <- E.try @(E.TypeError) do
    outer <- E.evaluate (P.fst unsupportedRoundTrip)
    inner <- E.evaluate (P.snd unsupportedRoundTrip)
    P.pure (outer, inner)
  case result of
    P.Left err
      | P.all (`List.isInfixOf` P.show err) ["No instance for", "Associative CounterexampleDay"] -> P.pure ()
      | P.otherwise -> E.throwIO err
    P.Right observed ->
      P.ioError (P.userError ("Unsupported Day associator was accepted; round trip returned " P.++ P.show observed))
