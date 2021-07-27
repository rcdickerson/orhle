{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.VerifierTests(htf_thisModulesTests) where

import Test.Framework

import Orhle
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
  Right (OrhleParseResult _ impls specs triple expected) -> do
    result <- verify (SpecImpEnv impls specs) triple
    assertVerifierResultMatches expected result

testImpFile fileName = do
  contents <- readFile $ "test" </> "resources" </> "imp" </> fileName
  parseAndTest contents

test_deterministicInvalid = testImpFile "deterministicInvalid.imp"
test_deterministicValid = testImpFile "deterministicValid.imp"
test_loopValid = testImpFile "loopValid.imp"
test_loopInvalid = testImpFile "loopInvalid.imp"
test_simpleValid = testImpFile "simpleValid.imp"
test_simpleInvalid = testImpFile "simpleInvalid.imp"
