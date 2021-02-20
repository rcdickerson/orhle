module Main where

import System.Exit
import Test.HUnit
import VerifierTests

main :: IO Counts
main = do
  verifierTests <- buildVerifierTests
  results       <- runTestTT verifierTests
  if (errors results + failures results == 0)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
