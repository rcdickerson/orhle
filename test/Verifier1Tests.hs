module Verifier1Tests where

import RHLEVerifier
import Test.HUnit
import Z3.Monad

assertValid :: AbductionResult -> Assertion
assertValid (Left _)  = assertFailure "Expected VALID but was INVALID"
assertValid (Right _) = return ()

assertInvalid :: AbductionResult -> Assertion
assertInvalid (Left _)  = return ()
assertInvalid (Right _) = assertFailure "Expected INVALID but was VALID"

deterministicValid = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertValid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  x2 := 4;              \
    \  if x2 == 3 then       \
    \    y2 := 300           \
    \  else                  \
    \    y2 := 3             "

deterministicInvalid = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertInvalid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  x2 := 3;              \
    \  if x2 == 3 then       \
    \    y2 := 300           \
    \  else                  \
    \    y2 := 3             "

simpleValid = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertValid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call x2 := randOdd()  \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "

simpleValid2 = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertValid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 4 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call x2 := randOdd()  \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "

simpleInvalid = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertInvalid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 4             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call x2 := randOdd()  \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "

simpleInvalid2 = do
  result <- evalZ3 $ verify1 =<< mkRHLETrip "true" progA progE "(= y1 y2)"
  assertInvalid result
  where
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call x2 := randEven() \
    \    pre true            \
    \    post x2 % 2 == 0;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "


verifier1Tests :: Test
verifier1Tests = TestList
       [ TestLabel "deterministicValid"   $ TestCase deterministicValid
       , TestLabel "deterministicInvalid" $ TestCase deterministicInvalid
       , TestLabel "simpleValid"          $ TestCase simpleValid
       , TestLabel "simpleValid2"         $ TestCase simpleValid2
       , TestLabel "simpleInvalid"        $ TestCase simpleInvalid
       , TestLabel "simpleInvalid2"       $ TestCase simpleInvalid2
       ]
