-- Run illustrative computations as part of `cabal test all`.
module Main where

import CategoryExamples qualified
import FreeExamples qualified
import KanExamples qualified
import MonoidalSketches ()
import RepresentableExamples qualified
import Prelude qualified as P

checks :: [(P.String, P.Bool)]
checks = CategoryExamples.checks P.++ KanExamples.checks P.++ FreeExamples.checks P.++ RepresentableExamples.checks

main :: P.IO ()
main = do
  P.mapM_ (\(label, ok) -> if ok then P.pure () else P.ioError (P.userError label)) checks
  P.putStrLn (P.show (P.length checks) P.++ " exploratory example checks passed.")
