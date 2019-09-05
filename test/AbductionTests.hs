module AbductionTests where

import Abduction
import Test.HUnit
import Z3.Monad
import Z3Util

assertSuccess :: AbductionResult -> Assertion
assertSuccess (Left reason) = assertFailure $
  "Expected successful abduction, but got: " ++ reason
assertSuccess (Right _) = return ()

noAbduction = do
  assertSuccess =<< evalZ3 abd
  where
    abd = do
      known  <- parseSMT "(= y 5)"
      post   <- parseSMT "(> y 0)"
      abduce ([], [known], [post])

singleAbduction = do
  assertSuccess =<< evalZ3 abd
  where
    abd = do
      known  <- parseSMT "(= y 5)"
      post   <- parseSMT "(= (+ y x) 10)"
      abduce (["x"], [known], [post])

abductionTests :: Test
abductionTests = TestList
    [ TestLabel "noAbduction" $ TestCase noAbduction ]
