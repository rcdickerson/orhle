module Orhle.AssertionTests where

import qualified Data.Set as Set
import Orhle
import Orhle.Assertion
import Test.HUnit

-- Some dummy names for testing
foo = TypedName (Name "foo" 0) Bool
bar = TypedName (Name "bar" 0) Int

testArithSubOverArith = let
  arith    = Add [(Num 5), (Var foo), (Var bar)]
  expected = Add [(Num 5), (Div (Var foo) (Var bar)), (Var bar)]
  actual   = subArith foo (Div (Var foo) (Var bar)) arith
  in TestCase $ assertEqual "arithmetic substitution" expected actual

testArithSubOverAssertion = let
  assertion = Not $ Gte (Add [(Num 5), (Var foo)]) (Var bar)
  expected  = Not $ Gte (Add [(Num 5), (Num 10)]) (Var bar)
  actual    = subArith foo (Num 10) assertion
  in TestCase $ assertEqual "arithmetic substitution" expected actual

testBasicFreeVars = let
  assertion = Imp (Atom foo) (Not (Lt (Num 5) (Var bar)))
  expected  = Set.fromList [foo, bar]
  actual    = freeVars assertion
  in TestCase $ assertEqual "free variables" expected actual

testFreeVarsOverQuantification = let
  assertion = Imp (Atom foo) (Forall [bar] $ Eq (Var bar) (Num 5))
  expected  = Set.fromList [foo] -- bar is not free, it is captured by the forall
  actual    = freeVars assertion
  in TestCase $ assertEqual "free variables" expected actual

assertionTests = TestList [ TestLabel "arithSubOverArith"     testArithSubOverArith
                          , TestLabel "arithSubOverAssertion" testArithSubOverAssertion
                          , TestLabel "basicFreeVars"         testBasicFreeVars
                          , TestLabel "freeVarsOverQuant"     testFreeVarsOverQuantification
                          ]
