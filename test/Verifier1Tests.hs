module Main where

import Lib
import Test.HUnit
import Z3.Monad

assertValid :: InterpResult -> Assertion
assertValid (IRSat _) = return ()
assertValid IRUnsat   = assertFailure "Expected VALID but was INVALID"

assertInvalid :: InterpResult -> Assertion
assertInvalid (IRSat _) = assertFailure "Expected INVALID but was VALID"
assertInvalid IRUnsat   = return ()

deterministicValid = do
  result <- evalZ3 $ verify1 trip
  assertValid result
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
  result <- evalZ3 $ verify1 trip
  assertInvalid result
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
  result <- evalZ3 $ verify1 trip
  assertValid result
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
  result <- evalZ3 $ verify1 trip
  assertValid result
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
  result <- evalZ3 $ verify1 trip
  assertInvalid result
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
  result <- evalZ3 $ verify1 trip
  assertInvalid result
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

main :: IO Counts
main = runTestTT $ TestList
       [ TestLabel "deterministicValid"   $ TestCase deterministicValid
       , TestLabel "deterministicInvalid" $ TestCase deterministicInvalid
       , TestLabel "simpleValid"          $ TestCase simpleValid
       , TestLabel "simpleValid2"         $ TestCase simpleValid2
       , TestLabel "simpleInvalid"        $ TestCase simpleInvalid
       , TestLabel "simpleInvalid2"       $ TestCase simpleInvalid2
       ]
