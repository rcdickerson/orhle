{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.FeatureLearning.CollectionUtilTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.FeatureLearning.CollectionUtil
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Vector ( Vector )
import qualified Data.Vector as Vector

test_subsetsOfSizeWithEmptySet =
  assertEqual (Set.empty :: Set (Set Int)) $ subsetsOfSize 5 Set.empty

test_subsetsOfSizeZero =
  assertEqual (Set.empty :: Set (Set Int)) $ subsetsOfSize 0 Set.empty

test_subsetsOfSizeOne = let
  expected = Set.fromList [ Set.singleton 1
                          , Set.singleton 2
                          , Set.singleton 3]
  actual = subsetsOfSize 1 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_subsetsOfSizeTwo = let
  expected = Set.fromList [ Set.fromList [1, 2]
                          , Set.fromList [1, 3]
                          , Set.fromList [2, 3]]
  actual = subsetsOfSize 2 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_subsetsOfSizeThree = let
  expected = Set.fromList [ Set.fromList [1, 2, 3] ]
  actual = subsetsOfSize 3 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_subsetsOfSizeFour = let
  expected = (Set.empty :: Set (Set Int))
  actual = subsetsOfSize 4 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_chooseWithReplacementWithEmptySet = let
  expected = (Set.empty :: Set [Int])
  actual = chooseWithReplacement 5 Set.empty
  in assertEqual expected actual

test_chooseWithReplacementWithSingletonSet = let
  expected = Set.fromList [ [1, 1, 1, 1, 1, 1, 1, 1, 1, 1] ]
  actual = chooseWithReplacement 10 $ Set.singleton 1
  in assertEqual expected actual

test_chooseWithReplacementZero = let
  expected = (Set.empty :: Set [Int])
  actual = chooseWithReplacement 0 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_chooseWithReplacement1 = let
  expected = Set.fromList [ [1], [2], [3] ]
  actual = chooseWithReplacement 1 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_chooseWithReplacement2 = let
  expected = Set.fromList [ [1, 1]
                          , [1, 2]
                          , [1, 3]
                          , [2, 1]
                          , [2, 2]
                          , [2, 3]
                          , [3, 1]
                          , [3, 2]
                          , [3, 3] ]
  actual = chooseWithReplacement 2 $ Set.fromList [1, 2, 3]
  in assertEqual expected actual

test_vecToSetEmpty = let
  expected = (Set.empty :: Set Int)
  actual = vecToSet (Vector.empty :: Vector Int)
  in assertEqual expected actual

test_vecToSet = let
  expected = Set.fromList [1, 2, 3]
  actual = vecToSet $ Vector.fromList [2, 3, 2, 1, 3, 1, 1]
  in assertEqual expected actual
