module Orhle.Imp.ImpParserTests where

import qualified Data.Map as Map
import Orhle.Imp
import Test.HUnit

-- Some dummy names / vs for convenience
n name = Name name 0
v = AVar . n
a = v "a"
b = v "b"
c = v "c"
x = n "x"
y = n "y"
z = n "z"

-- Return value name constructor for convenience
rv i = Name "retVal" i

assertCorrectParse :: String -> Program -> Assertion
assertCorrectParse progStr expected = case parseImp progStr of
  Left err        -> assertFailure $ "Parse error: " ++ (show err)
  Right (prog, _) -> assertEqual "parsed program" expected prog

assertCorrectFunParse :: String -> CallId -> FunImpl -> Assertion
assertCorrectFunParse progStr funId expected = case parseImp progStr of
  Left err         -> assertFailure $ "Parse error: " ++ (show err)
  Right (_, impls) -> case Map.lookup funId impls of
    Nothing   -> assertFailure $ "Function implementation not found: " ++ funId
    Just impl -> assertEqual "parsed program" expected impl

testEmptyProg = let
  prog = "skip;"
  expected = SSkip
  in TestCase $ assertCorrectParse prog expected

testSingleAssignee = let
  prog = "x := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [x]
  in TestCase $ assertCorrectParse prog expected

testMultipleAssignees = let
  prog = "(x, y, z) := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [x, y, z]
  in TestCase $ assertCorrectParse prog expected

testArrayAssignees = let
  prog = "(x[3], y, z[2]) := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [n"x_0", n"x_1", n"x_2", y, n"z_0", n"z_1"]
  in TestCase $ assertCorrectParse prog expected

testSingleArrayAssignee = let
  prog = "x[3] := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [n"x_0", n"x_1", n"x_2"]
  in TestCase $ assertCorrectParse prog expected

testMultipleReturns = let
  prog = "fun foo() { return (a, b, c); }"
  expectedBody = SSeq [ SAsgn (rv 2) a
                      , SAsgn (rv 1) b
                      , SAsgn (rv 0) c
                      ]
  expected = FunImpl [] expectedBody [rv 2, rv 1, rv 0]
  in TestCase $ assertCorrectFunParse prog "foo" expected

testSingleArrayReturn = let
  prog = "fun foo() { return x[3]; }"
  expectedBody = SSeq [ SAsgn (rv 2) (v "x_0")
                      , SAsgn (rv 1) (v "x_1")
                      , SAsgn (rv 0) (v "x_2")
                      ]
  expected = FunImpl [] expectedBody [rv 2, rv 1, rv 0]
  in TestCase $ assertCorrectFunParse prog "foo" expected


testArrayReturns = let
  prog = "fun foo() { return (x[3], b, z[2]); }"
  expectedBody = SSeq [ SAsgn (rv 5) (v "x_0")
                      , SAsgn (rv 4) (v "x_1")
                      , SAsgn (rv 3) (v "x_2")
                      , SAsgn (rv 2) b
                      , SAsgn (rv 1) (v "z_0")
                      , SAsgn (rv 0) (v "z_1")
                      ]
  expected = FunImpl [] expectedBody [rv 5, rv 4, rv 3, rv 2, rv 1, rv 0]
  in TestCase $ assertCorrectFunParse prog "foo" expected

testArrayArgs = let
  prog = "y := call foo (x[3]); }"
  expected = SCall "foo" [v"x_0", v"x_1", v"x_2"] [y]
  in TestCase $ assertCorrectParse prog expected

impParserTests = TestList [ TestLabel "testEmptyProg"           testEmptyProg
                          , TestLabel "testSingleAssignee"      testSingleAssignee
                          , TestLabel "testMultipleAssignees"   testMultipleAssignees
                          , TestLabel "testArrayAssignees"      testArrayAssignees
                          , TestLabel "testSingleArrayAssignee" testSingleArrayAssignee
                          , TestLabel "testMultipleReturns"     testMultipleReturns
                          , TestLabel "testSingleArrayReturn"   testSingleArrayReturn
                          , TestLabel "testArrayReturns"        testArrayReturns
                          , TestLabel "testArrayArgs"           testArrayArgs
                          ]
