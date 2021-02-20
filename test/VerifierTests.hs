module VerifierTests where

import Data.List        (isSuffixOf)
import Orhle
import System.Directory (getDirectoryContents)
import System.FilePath
import Test.HUnit

assertVerifierResultMatches :: OAExpectedResult -> VerifierResult -> Assertion
assertVerifierResultMatches expected (result, trace) =
  case (expected, result) of
    (OASuccess, Right _)   -> return ()
    (OAFailure, Left  _)   -> return ()
    (OASuccess, Left  msg) -> assertFailure
      $ "Expected VALID but was INVALID\n" ++ msg ++ "\n" ++ (ppVTrace trace)
    (OAFailure, Right msg) -> assertFailure
      $ "Expected INVALID but was VALID\n" ++ msg ++ "\n" ++ (ppVTrace trace)


parseAndTest :: String -> Assertion
parseAndTest progStr = case parseOrhleApp progStr of
  Left  err -> assertFailure $ "Parse error: " ++ (show err)
  Right (_, query, expected) -> do
    let specsAndTrip = do
          (OAQuery specs pre forallProgs existsProgs post) <- query
          return (specs, RHLETrip pre forallProgs existsProgs post)
    result <- rhleVerifier specsAndTrip
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
buildVerifierTests = buildTestCases $ "test" </> "imp"
