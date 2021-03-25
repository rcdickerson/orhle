module Orhle.InlinerTests where

import qualified Data.Map as Map
import Orhle
import Orhle.Imp
import Test.HUnit

-- Some dummy names / aexps
a = (Name "a" 0)
b = (Name "b" 0)
c = (Name "c" 0)
d = (Name "d" 0)
x = (Name "x" 0)
y = (Name "y" 0)

testSimpleInline = let
  idImpls = Map.fromList [
      ("foo", FunImpl [x] (SAsgn y (AVar x)) [y])
    , ("bar", FunImpl [x] (SAsgn y (AVar x)) [y])
    , ("baz", FunImpl [x] (SAsgn y (AVar x)) [y])]
  prog = SSeq [
      SCall "foo" [AVar a] [b]
    , SCall "bar" [AVar b] [c]
    , SCall "baz" [AVar c] [d]]
  expected = Right $ SSeq [
    SSeq [ -- SCall foo
           SAsgn (Name "x" 1) (AVar a)
         , SAsgn (Name "y" 1) (AVar (Name "x" 1))
         , SAsgn b (AVar (Name "y" 1))
         ],
    SSeq [ -- SCall bar
           SAsgn (Name "x" 2) (AVar b)
         , SAsgn (Name "y" 2) (AVar (Name "x" 2))
         , SAsgn c (AVar (Name "y" 2))
         ],
    SSeq [ -- SCall baz
           SAsgn (Name "x" 3) (AVar c)
         , SAsgn (Name "y" 3) (AVar (Name "x" 3))
         , SAsgn d (AVar (Name "y" 3))
         ]
    ]
  actual = inline idImpls prog
  in TestCase $ assertEqual "inlining" expected actual

testNestedInline = let
  bodyFoo = SAsgn y (AAdd (AVar x) (ALit 1))
  idImpls = Map.fromList [
      ("foo", FunImpl [x] bodyFoo [y])
    , ("bar", FunImpl [x] (SCall "foo" [AVar x] [y]) [y])
    , ("baz", FunImpl [x] (SCall "bar" [AVar x] [y]) [y])]
  prog = SCall "baz" [AVar a] [b]
  expected = Right $
    SSeq [ -- SCall baz
           SAsgn (Name "x" 1) (AVar a)
         , SSeq [ -- SCall bar
               SAsgn (Name "x" 2) (AVar (Name "x" 1))
             , SSeq [ -- SCall foo
                   SAsgn (Name "x" 3) (AVar (Name "x" 2))
                 , SAsgn (Name "y" 3) (AAdd (AVar (Name "x" 3)) (ALit 1))
                 , SAsgn (Name "y" 2) (AVar (Name "y" 3))
                 ]
             , SAsgn (Name "y" 1) (AVar (Name "y" 2))
             ]
         , SAsgn b (AVar (Name "y" 1))
         ]
  actual = inline idImpls prog
  in TestCase $ assertEqual "inlining" expected actual

testNoRecursion = let
  impls = Map.fromList [
    ("foo", FunImpl [x] (SCall "foo" [AVar x] [y]) [y])
    ]
  prog = SCall "foo" [AVar a] [b]
  expected = Left "Cannot inline recursive call to foo"
  actual   = inline impls prog
  in TestCase $ assertEqual "inlining" expected actual

testMultipleReturns = let
  idImpls = Map.fromList [
      ("foo", FunImpl [x] (SAsgn y (AVar x)) [x, y])]
  prog = SSeq [
      SCall "foo" [AVar a] [b, c]]
  expected = Right $ SSeq [
    SSeq [ -- params
           SAsgn (Name "x" 1) (AVar a)
           -- body
         , SAsgn (Name "y" 1) (AVar (Name "x" 1))
           -- returns
         , SAsgn (Name "b" 0) (AVar (Name "x" 1))
         , SAsgn (Name "c" 0) (AVar (Name "y" 1))
         ]
    ]
  actual = inline idImpls prog
  in TestCase $ assertEqual "inlining" expected actual

inlinerTests = TestList [ TestLabel "testSimpleInline"    testSimpleInline
                        , TestLabel "testNestedInline"    testNestedInline
                        , TestLabel "testNoRecursion"     testNoRecursion
                        , TestLabel "testMultipleReturns" testMultipleReturns
                        ]
