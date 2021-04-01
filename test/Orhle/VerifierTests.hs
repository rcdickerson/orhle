{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.VerifierTests(htf_thisModulesTests) where

import Test.Framework

import Data.List        (isSuffixOf)
import qualified Data.Map as Map
import Orhle
import System.Directory (getDirectoryContents)
import System.FilePath

assertVerifierResultMatches expected result =
  case (expected, result) of
    (ExpectSuccess, Right _)   -> return ()
    (ExpectFailure, Left  _)   -> return ()
    (ExpectSuccess, Left (Orhle.Failure msg)) -> assertFailure
      $ "Expected VALID but was INVALID. Error: " ++ msg
    (ExpectFailure, Right _) -> assertFailure
      $ "Expected INVALID but was VALID"

parseAndTest progStr = case parseOrhle progStr of
  Left  err -> assertFailure $ "Parse error: " ++ (show err)
  Right (_, _, specs, triple, expected) -> do
    result <- verify specs Map.empty triple
    assertVerifierResultMatches expected result

testImpFile fileName = do
  contents <- readFile $ "test" </> "resources" </> "imp" </> fileName
  parseAndTest contents

test_deterministicInvalid = testImpFile "deterministicInvalid.imp"
test_deterministicValid = testImpFile "deterministicValid.imp"
test_simpleInvalid = testImpFile "simpleInvalid.imp"
test_simpleValid = testImpFile "simpleValid.imp"
