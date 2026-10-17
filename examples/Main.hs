-- Run illustrative computations as part of `cabal test all`.
module Main where

import ApplicativeClient qualified
import CategoryExamples qualified
import FreeExamples qualified
import KanExamples qualified
import MonoidalSketches ()
import Quickstart ()
import RepresentableExamples qualified
import Prelude qualified as P

checks :: [(P.String, P.Bool)]
checks =
  CategoryExamples.checks
    P.++ KanExamples.checks
    P.++ FreeExamples.checks
    P.++ RepresentableExamples.checks
    P.++ [("Applicative client derives the constraint from its operations", ApplicativeClient.example P.== P.Just (7, P.True))]

main :: P.IO ()
main = do
  P.mapM_ (\(label, ok) -> if ok then P.pure () else P.ioError (P.userError label)) checks
  P.putStrLn (P.show (P.length checks) P.++ " example checks passed.")
