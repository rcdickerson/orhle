module Verifier2Tests where

import RHLEVerifier
import Test.HUnit
import Z3.Monad

assertValid :: String -> Prog -> Prog -> String -> Assertion
assertValid pre progA progE post = do
  (result, tr) <- evalZ3 $ verify2 =<< mkRHLETrip pre progA progE post
  trace <- evalZ3 $ ppVTrace tr
  case result of
    Right _ -> return ()
    Left r  -> assertFailure
      $ "Expected VALID but was INVALID: " ++ r ++ "\n" ++ trace

assertInvalid :: String -> Prog -> Prog -> String -> Assertion
assertInvalid pre progA progE post = do
  (result, tr) <- evalZ3 $ verify2 =<< mkRHLETrip pre progA progE post
  trace <- evalZ3 $ ppVTrace tr
  case result of
    Left  _ -> return ()
    Right _ -> assertFailure
      $ "Expected INVALID but was VALID\n" ++ trace

deterministicValid = do
  assertValid "true" progA progE "(= y1 y2)"
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
  assertInvalid "true" progA progE "(= y1 y2)"
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
  assertValid "true" progA progE "(= y1 y2)"
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
  assertValid "true" progA progE "(= y1 y2)"
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
  assertInvalid "true" progA progE "(= y1 y2)"
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
  assertInvalid "true" progA progE "(= y1 y2)"
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

verifier2Tests :: Test
verifier2Tests = TestList
       [ TestLabel "deterministicValid"   $ TestCase deterministicValid
       , TestLabel "deterministicInvalid" $ TestCase deterministicInvalid
       , TestLabel "simpleValid"          $ TestCase simpleValid
       , TestLabel "simpleValid2"         $ TestCase simpleValid2
       , TestLabel "simpleInvalid"        $ TestCase simpleInvalid
       , TestLabel "simpleInvalid2"       $ TestCase simpleInvalid2
       ]
