module Verifier2Tests where

import Lib
import Test.HUnit
import Z3.Monad

assertValid :: RHLETrip -> Assertion
assertValid trip = do
  (result, tr) <- evalZ3 $ verify2 trip
  trace <- evalZ3 $ ppVTrace tr
  case result of
    Valid   _ -> return ()
    Invalid r -> assertFailure
      $ "Expected VALID but was INVALID: " ++ r ++ "\n" ++ trace

assertInvalid :: RHLETrip -> Assertion
assertInvalid trip = do
  (result, tr) <- evalZ3 $ verify2 trip
  trace <- evalZ3 $ ppVTrace tr
  case result of
    Invalid _ -> return ()
    Valid   _ -> assertFailure
      $ "Expected INVALID but was VALID\n" ++ trace

deterministicValid = do
  assertValid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

deterministicInvalid = do
  assertInvalid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleValid = do
  assertValid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleValid2 = do
  assertValid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleInvalid = do
  assertInvalid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleInvalid2 = do
  assertInvalid trip
  where
    pre   = CTrue
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
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

verifier2Tests :: Test
verifier2Tests = TestList
       [ TestLabel "deterministicValid"   $ TestCase deterministicValid
       , TestLabel "deterministicInvalid" $ TestCase deterministicInvalid
       , TestLabel "simpleValid"          $ TestCase simpleValid
       , TestLabel "simpleValid2"         $ TestCase simpleValid2
       , TestLabel "simpleInvalid"        $ TestCase simpleInvalid
       , TestLabel "simpleInvalid2"       $ TestCase simpleInvalid2
       ]