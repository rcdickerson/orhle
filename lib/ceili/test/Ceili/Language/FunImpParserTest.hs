{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.Language.FunImpParserTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Language.FunImp
import Ceili.Language.FunImpParser
import qualified Data.Map as Map

-- Some dummy names / vars for convenience
n name = Name name 0
x = n "x"
y = n "y"

assertCorrectParse progStr expected =
  case parseFunImp progStr of
    Left err     -> assertFailure $ "Parse error: " ++ (show err)
    Right actual -> assertEqual expected actual

test_funDef = let
  prog = "fun foo(x) { x := 0; return x; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimpl_params = [x],
                      fimpl_body = impSeq @Integer [
                         impAsgn x (ALit 0),
                         impAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]})]
  in assertCorrectParse prog expected

test_twoFuns = let
  prog = "fun foo(x) { x := 0; return x; } \
        \ fun bar(y) { y := 5; return y; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimpl_params = [x],
                      fimpl_body = impSeq @Integer [
                         impAsgn x (ALit 0),
                         impAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]}),
     ("bar", FunImpl{ fimpl_params = [y],
                      fimpl_body = impSeq [
                         impAsgn y (ALit 5),
                         impAsgn (Name "bar!retVal" 0) (AVar y)],
                      fimpl_returns = [Name "bar!retVal" 0]})]
  in assertCorrectParse prog expected

test_funCall = let
  prog = "fun foo(x) { x := foo(x); return x; }"
  expected = Map.fromList
    [("foo", FunImpl{ fimpl_params = [x],
                      fimpl_body = impSeq @Integer [
                         impCall "foo" [AVar x] [x],
                         impAsgn (Name "foo!retVal" 0) (AVar x)],
                      fimpl_returns = [Name "foo!retVal" 0]})]
  in assertCorrectParse prog expected
