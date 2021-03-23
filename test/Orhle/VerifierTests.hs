module Orhle.VerifierTests where

import Data.List        (isSuffixOf)
import qualified Data.Map as Map
import Orhle
import System.Directory (getDirectoryContents)
import System.FilePath
import Test.HUnit

assertVerifierResultMatches :: ExpectedResult -> (Either Failure Success) -> Assertion
assertVerifierResultMatches expected result =
  case (expected, result) of
    (ExpectSuccess, Right _)   -> return ()
    (ExpectFailure, Left  _)   -> return ()
    (ExpectSuccess, Left (Failure _ model)) -> assertFailure
      $ "Expected VALID but was INVALID\n" ++ "model: " ++ model
    (ExpectFailure, Right _) -> assertFailure
      $ "Expected INVALID but was VALID"

parseAndTest :: String -> Assertion
parseAndTest progStr = case parseOrhle progStr of
  Left  err -> assertFailure $ "Parse error: " ++ (show err)
  Right (_, _, specs, triple, expected) -> do
    result <- verify specs Map.empty triple
    assertVerifierResultMatches expected result

readImpFiles :: FilePath -> IO [(String, String)]
readImpFiles dirName = do
  fileNames <- getDirectoryContents dirName
  let impFiles = filter (\f -> "imp" `isSuffixOf` f) fileNames
  contents <- mapM (\f -> readFile $ dirName </> f) impFiles
  return $ zip impFiles contents

buildTestCases :: FilePath -> IO Test
buildTestCases dirName = do
  impFiles <- readImpFiles dirName
  let buildTestCase (name, contents) = TestLabel name $ TestCase (parseAndTest contents)
  return . TestList $ map buildTestCase impFiles

buildVerifierTests :: IO Test
buildVerifierTests = buildTestCases $ "test" </> "resources" </> "imp"
