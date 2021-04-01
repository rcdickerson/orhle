{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.AssertionTests(htf_thisModulesTests) where

import Test.Framework

import qualified Data.Set as Set
import Orhle
import Orhle.Assertion

-- Some dummy names for testing
foo = TypedName (Name "foo" 0) Bool
bar = TypedName (Name "bar" 0) Int

test_arithSubOverArith = let
  arith    = Add [(Num 5), (Var foo), (Var bar)]
  expected = Add [(Num 5), (Div (Var foo) (Var bar)), (Var bar)]
  actual   = subArith foo (Div (Var foo) (Var bar)) arith
  in assertEqual expected actual

test_arithSubOverAssertion = let
  assertion = Not $ Gte (Add [(Num 5), (Var foo)]) (Var bar)
  expected  = Not $ Gte (Add [(Num 5), (Num 10)]) (Var bar)
  actual    = subArith foo (Num 10) assertion
  in assertEqual expected actual

test_basicFreeVars = let
  assertion = Imp (Atom foo) (Not (Lt (Num 5) (Var bar)))
  expected  = Set.fromList [foo, bar]
  actual    = freeVars assertion
  in assertEqual expected actual

test_freeVarsOverQuantification = let
  assertion = Imp (Atom foo) (Forall [bar] $ Eq (Var bar) (Num 5))
  expected  = Set.fromList [foo] -- bar is not free, it is captured by the forall
  actual    = freeVars assertion
  in assertEqual expected actual
