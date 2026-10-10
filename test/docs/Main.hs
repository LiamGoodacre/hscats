module Main (main) where

import qualified ApplicativeClient
import qualified ApplicativeUsage
import Control.Monad (unless)
import Data.List (isPrefixOf, stripPrefix)
import qualified DoUsage
import qualified PullbackUsage
import qualified Quickstart
import qualified SliceUsage

-- Compile the snippets in this separate component without library extensions.
-- Compare them with the published text so changing either side requires an
-- update to the other. Only the added module declaration and blank lines differ.
normalize :: [String] -> [String]
normalize = filter (not . null) . filter (not . isPrefixOf "module ")

checkSnippet :: String -> [String] -> IO ()
checkSnippet name published = do
  compiled <- lines <$> readFile ("test/docs/" ++ name ++ ".hs")
  unless (normalize published == normalize compiled) $
    ioError (userError (name ++ " differs from its published example"))

checkHaddock :: String -> String -> IO ()
checkHaddock path name = do
  source <- lines <$> readFile path
  case dropWhile (/= "-- @") source of
    [] -> ioError (userError ("No example block in " ++ path))
    _ : rest -> do
      let code = takeWhile (/= "-- @") rest
          uncomment line = case stripPrefix "-- " line of
            Just body -> body
            Nothing | line == "--" -> ""
            Nothing -> error ("Malformed example line in " ++ path)
      unless (not (null code) && "-- @" `elem` rest) $
        ioError (userError ("Unterminated example block in " ++ path))
      checkSnippet name (map uncomment code)

main :: IO ()
main = do
  checkHaddock "lib/Cats/Applicative.hs" "ApplicativeUsage"
  checkHaddock "lib/Cats/Do.hs" "DoUsage"
  checkHaddock "lib/Cats/Pullback.hs" "PullbackUsage"
  checkHaddock "lib/Cats/Slice.hs" "SliceUsage"
  readme <- lines <$> readFile "README.md"
  case dropWhile (/= "```haskell") readme of
    [] -> ioError (userError "No Haskell example in README.md")
    _ : rest -> do
      unless ("```" `elem` rest) (ioError (userError "Unterminated README example"))
      checkSnippet "Quickstart" (takeWhile (/= "```") rest)
  unless
    ( ApplicativeUsage.combinations == [11, 21, 12, 22]
        && ApplicativeUsage.fallback == Just "7"
        && DoUsage.example == [11, 12]
        && ApplicativeClient.example == Just (7, True)
        && PullbackUsage.example == (8, False)
        && SliceUsage.example == 3
    )
    (ioError (userError "A documentation or client example returned an unexpected result"))
  Quickstart.main
  putStrLn "5 published snippets compile and match; 6 usage checks passed."
