{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.FeatureLearning.SeparatorTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities
import Ceili.FeatureLearning.Separator
import Ceili.Name
import Ceili.ProgState
import Ceili.SMTString
import qualified Data.Map as Map
import qualified Data.Set as Set

runAndAssertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                       => Assertion t
                       -> Ceili (Maybe (Assertion t))
                       -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili emptyEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing     -> assertFailure "Expected assertion, got Nothing."
        Just assertion -> assertEquivalent expected assertion


test_featureLearn = let
  x         = Name "x" 0
  names     = Set.singleton x
  lits      = Set.fromList [1, 5, -1, -5] :: Set.Set Integer
  goodTests = [ Map.fromList [(Name "x" 0, 1)]
              , Map.fromList [(Name "x" 0, 5)] ] :: [ProgState Integer]
  badTests  = [ Map.fromList [(Name "x" 0, -1)]
              , Map.fromList [(Name "x" 0, -5)] ] :: [ProgState Integer]
  expected  = Lt (Num 0) (Var x)
  in runAndAssertEquivalent expected $ findSeparator 1 (linearInequalities lits names) goodTests badTests
