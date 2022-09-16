{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.FeatureLearning.FeatureVectorTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.FeatureVector
import qualified Data.Map as Map
import qualified Data.Vector as Vector

test_createFV = let
  x = Var $ Name "x" 0
  assertions = Vector.fromList [Eq @Integer x (Num 0), Lt x (Num 3), Lte x (Num 3)]
  states = Vector.fromList [ Map.fromList [(Name "x" 0, 0)]
                           , Map.fromList [(Name "x" 0, 2)]
                           , Map.fromList [(Name "x" 0, 3)]
                           ]
  expected = Vector.fromList [ Vector.fromList [True,  True,  True]
                             , Vector.fromList [False, True,  True]
                             , Vector.fromList [False, False, True]
                             ]
  in do
    result <- runCeili emptyEnv $ createFV assertions states
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual
