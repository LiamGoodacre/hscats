{-# OPTIONS_GHC -fdefer-type-errors -Wno-deferred-type-errors #-}

module ProcomposeUnsupported (check) where

import Cats
import Control.Exception qualified as E
import Data.List qualified as List
import DayChecks (Add (..))
import Prelude qualified as P

-- Generic explicit unit maps are available, but their reverse round trips
-- change observable representatives. Do not promise a Monoidal instance.
unsupported :: DataProcompose (Hom Add) (Hom Add) '() '()
unsupported = (coidl @_ @(Procompose₁ @Add) @(Hom Add) $$ ((), ())) (Add 3)

check :: P.IO ()
check = do
  result <- E.try @E.TypeError (E.evaluate unsupported)
  case result of
    P.Left err
      | P.all (`List.isInfixOf` P.show err) ["No instance for", "Monoidal", "Procompose"] -> P.pure ()
      | P.otherwise -> E.throwIO err
    P.Right _ -> P.ioError (P.userError "Unsupported generic Procompose Monoidal instance was accepted")
