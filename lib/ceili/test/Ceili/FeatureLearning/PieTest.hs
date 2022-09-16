{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.FeatureLearning.PieTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities ( linearInequalities )
import Ceili.FeatureLearning.Pie
import Ceili.SMTString
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Vector as Vector

runAndAssertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                       => Assertion t -> Ceili (Maybe (Assertion t)) -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili emptyEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing        -> assertFailure "Expected assertion, got Nothing."
        Just assertion -> assertEquivalent expected assertion


test_getConflict_noConflicts = let
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  False, False]
                           , Vector.fromList [False, False, True]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  in assertEqual Nothing $ getConflict negFVs posFVs badTests goodTests

test_getConflict_oneConflict = let
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  False, False]
                           , Vector.fromList [True,  True,  False]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, False, True]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 5)] ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 2)] ]
  expected = Just (expectedXBad, expectedXGood)
  in assertEqual expected $ getConflict negFVs posFVs badTests goodTests

test_getConflict_twoGoodConflicts = let
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [False, False, True]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)] ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                                  , Map.fromList [(Name "x" 0, 2)]
                                  ]
  expected = Just (expectedXBad, expectedXGood)
  in assertEqual expected $ getConflict negFVs posFVs badTests goodTests

test_getConflict_twoBadConflicts = let
  negFVs = Vector.fromList [ Vector.fromList [True,  True, False]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [False, False, True]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]

  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                                 , Map.fromList [(Name "x" 0, 3)]
                                 ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)] ]
  expected = Just (expectedXBad, expectedXGood)
  in assertEqual expected $ getConflict negFVs posFVs badTests goodTests

test_getConflict_twoConflictsEach = let
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True, False]
                           , Vector.fromList [True,  True, False]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)]
                                 , Map.fromList [(Name "x" 0, 5)]
                                 ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                                  , Map.fromList [(Name "x" 0, 2)]
                                  ]
  expected = Just (expectedXBad, expectedXGood)
  in assertEqual expected $ getConflict negFVs posFVs badTests goodTests

test_getConflict_twoPossibleAnswers = let
  negFVs = Vector.fromList [ Vector.fromList [False, False, True]
                           , Vector.fromList [True,  True,  False]
                           , Vector.fromList [True, False, True]
                           ]
  posFVs = Vector.fromList [ Vector.fromList [True, True,  False]
                           , Vector.fromList [True, False, False]
                           , Vector.fromList [True, False, True]
                           ]
  badTests = Vector.fromList [ Map.fromList [(Name "x" 0, 1)]
                             , Map.fromList [(Name "x" 0, 3)]
                             , Map.fromList [(Name "x" 0, 5)]
                             ]
  goodTests = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                              , Map.fromList [(Name "x" 0, 2)]
                              , Map.fromList [(Name "x" 0, 4)]
                              ]
  expectedXBad = Vector.fromList [ Map.fromList [(Name "x" 0, 3)] ]
  expectedXGood = Vector.fromList [ Map.fromList [(Name "x" 0, 0)] ]
  expected = Just (expectedXBad, expectedXGood)
  in assertEqual expected $ getConflict negFVs posFVs badTests goodTests

test_pie = let
  x         = Name "x" 0
  names     = Set.singleton x
  lits      = Set.empty
  badTests  = [ Map.fromList [(Name "x" 0,  0)]
              , Map.fromList [(Name "x" 0, -1)]
              , Map.fromList [(Name "x" 0, -5)] ]
  goodTests = [ Map.fromList [(Name "x" 0, 1)]
              , Map.fromList [(Name "x" 0, 5)] ]
  expected  = Lt @Integer (Num 0) (Var x)
  in runAndAssertEquivalent expected $ pie Set.empty (linearInequalities lits) badTests goodTests


--
-- NB: Full LoopInvGen tests are expensive and are thus located in the verification-test suite.
--
