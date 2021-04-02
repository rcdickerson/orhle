{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.Imp.ImpParserTests(htf_thisModulesTests) where

import Test.Framework

import qualified Data.Map as Map
import Orhle.Imp

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
rv funName i = Name (funName ++ "!retVal") i

assertCorrectParse progStr expected = case parseImp progStr of
  Left err        -> assertFailure $ "Parse error: " ++ (show err)
  Right (prog, _) -> assertEqual expected prog

assertCorrectFunParse progStr funId expected = case parseImp progStr of
  Left err         -> assertFailure $ "Parse error: " ++ (show err)
  Right (_, impls) -> case Map.lookup funId impls of
    Nothing   -> assertFailure $ "Function implementation not found: " ++ funId
    Just impl -> assertEqual expected impl

test_emptyProg = let
  prog = "skip;"
  expected = SSkip
  in assertCorrectParse prog expected

test_singleAssignee = let
  prog = "x := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [x]
  in assertCorrectParse prog expected

test_multipleAssignees = let
  prog = "(x, y, z) := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [x, y, z]
  in assertCorrectParse prog expected

test_arrayAssignees = let
  prog = "(x[3], y, z[2]) := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [n"x_0", n"x_1", n"x_2", y, n"z_0", n"z_1"]
  in assertCorrectParse prog expected

test_singleArrayAssignee = let
  prog = "x[3] := call foo(a, b, c);"
  expected = SCall "foo" [a, b, c] [n"x_0", n"x_1", n"x_2"]
  in assertCorrectParse prog expected

test_multipleReturns = let
  prog = "fun foo() { return (a, b, c); }"
  expectedBody = SSeq [ SAsgn (rv "foo" 2) a
                      , SAsgn (rv "foo" 1) b
                      , SAsgn (rv "foo" 0) c
                      ]
  expected = FunImpl [] expectedBody [rv "foo" 2, rv "foo" 1, rv "foo" 0]
  in assertCorrectFunParse prog "foo" expected

test_singleArrayReturn = let
  prog = "fun foo() { return x[3]; }"
  expectedBody = SSeq [ SAsgn (rv "foo" 2) (v "x_0")
                      , SAsgn (rv "foo" 1) (v "x_1")
                      , SAsgn (rv "foo" 0) (v "x_2")
                      ]
  expected = FunImpl [] expectedBody [rv "foo" 2, rv "foo" 1, rv "foo" 0]
  in assertCorrectFunParse prog "foo" expected


test_arrayReturns = let
  prog = "fun foo() { return (x[3], b, z[2]); }"
  expectedBody = SSeq [ SAsgn (rv "foo" 5) (v "x_0")
                      , SAsgn (rv "foo" 4) (v "x_1")
                      , SAsgn (rv "foo" 3) (v "x_2")
                      , SAsgn (rv "foo" 2) b
                      , SAsgn (rv "foo" 1) (v "z_0")
                      , SAsgn (rv "foo" 0) (v "z_1")
                      ]
  expected = FunImpl [] expectedBody $ [ rv "foo" 5
                                       , rv "foo" 4
                                       , rv "foo" 3
                                       , rv "foo" 2
                                       , rv "foo" 1
                                       , rv "foo" 0
                                       ]
  in assertCorrectFunParse prog "foo" expected

test_arrayArgs = let
  prog = "y := call foo (x[3]); }"
  expected = SCall "foo" [v"x_0", v"x_1", v"x_2"] [y]
  in assertCorrectParse prog expected
