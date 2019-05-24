module Main where

import Lib
import Test.HUnit
import Z3.Monad

simpleValid = do
  result <- evalZ3 $ verify trip
  (assertEqual "valid" result True)
  where
    pre   = CTrue
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call randOdd(x2)      \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleValid2 = do
  result <- evalZ3 $ verify trip
  (assertEqual "valid" result True)
  where
    pre   = CTrue
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 4 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call randOdd(x2)      \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleInvalid = do
  result <- evalZ3 $ verify trip
  (assertEqual "valid" result False)
  where
    pre   = CTrue
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 4             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call randOdd(x2)      \
    \    pre true            \
    \    post x2 % 2 == 1;   \
    \  if x2 == 3 then       \
    \    y2 := 3             \
    \  else                  \
    \    y2 := 300           "
    post = (CEq (V "y1") (V "y2"))
    trip = RHLETrip pre progA progE post

simpleInvalid2 = do
  result <- evalZ3 $ verify trip
  (assertEqual "valid" result False)
  where
    pre   = CTrue
    progA = parseImpOrError "\
    \  x1 := 3;              \
    \  if x1 == 3 then       \
    \    y1 := 3             \
    \  else                  \
    \    y1 := 300           "
    progE = parseImpOrError "\
    \  call randEven(x2)      \
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
       [ TestLabel "simpleValid"    $ TestCase simpleValid
       , TestLabel "simpleValid2"   $ TestCase simpleValid2
       , TestLabel "simpleInvalid"  $ TestCase simpleInvalid
       , TestLabel "simpleInvalid2" $ TestCase simpleInvalid2
       ]
