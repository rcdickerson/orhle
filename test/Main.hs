module Main where

import RHLEVerifier
import Test.HUnit
import Z3.Monad

import Verifier1Tests
import Verifier2Tests

main :: IO Counts
main = runTestTT $ TestList
  [ --verifier1Tests
  verifier2Tests
  ]
