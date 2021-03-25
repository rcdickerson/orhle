module Main where

import Orhle.AssertionTests     ( assertionTests )
import Orhle.Imp.ImpParserTests ( impParserTests )
import Orhle.InlinerTests       ( inlinerTests )
import Orhle.VerifierTests      ( buildVerifierTests )
import System.Exit
import Test.HUnit

main :: IO Counts
main = do
  verifierTests <- buildVerifierTests
  results       <- runTestTT $ TestList [ assertionTests
                                        , impParserTests
                                        , inlinerTests
                                        , verifierTests
                                        ]
  if (errors results + failures results == 0)
    then exitWith ExitSuccess
    else exitWith (ExitFailure 1)
