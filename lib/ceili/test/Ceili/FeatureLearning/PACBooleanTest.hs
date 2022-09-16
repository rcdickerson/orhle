{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.FeatureLearning.PACBooleanTest(htf_thisModulesTests) where

import Ceili.TestUtil
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.PACBoolean
import qualified Data.Map as Map
import Data.Vector ( Vector )
import qualified Data.Vector as Vector


-------------
-- Clauses --
-------------

test_clausesWithSize_0_0 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 0 0

test_clausesWithSize_1_0 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 1 0

test_clausesWithSize_0_1 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 0 1

test_clausesWithSize_5_1 =
  assertEqual (Vector.empty :: Vector Clause) $ clausesWithSize 5 1

test_clausesWithSize_1_1 =
  let expected = Vector.fromList [ Map.singleton 0 CPos
                                 , Map.singleton 0 CNeg ]
  in assertHasSameItems expected $ clausesWithSize 1 1

test_clausesWithSize_1_2 =
  let expected = Vector.fromList [ Map.singleton 0 CPos
                                 , Map.singleton 1 CPos
                                 , Map.singleton 0 CNeg
                                 , Map.singleton 1 CNeg]
  in assertHasSameItems expected $ clausesWithSize 1 2

test_clausesWithSize_2_3 =
  let expected = Vector.fromList [ -- 0, 1 combos
                                   Map.fromAscList [(0, CPos), (1, CPos)]
                                 , Map.fromAscList [(0, CPos), (1, CNeg)]
                                 , Map.fromAscList [(0, CNeg), (1, CPos)]
                                 , Map.fromAscList [(0, CNeg), (1, CNeg)]
                                   -- 0, 2 combos
                                 , Map.fromAscList [(0, CPos), (2, CPos)]
                                 , Map.fromAscList [(0, CPos), (2, CNeg)]
                                 , Map.fromAscList [(0, CNeg), (2, CPos)]
                                 , Map.fromAscList [(0, CNeg), (2, CNeg)]
                                   -- 1, 2 combos
                                 , Map.fromAscList [(1, CPos), (2, CPos)]
                                 , Map.fromAscList [(1, CPos), (2, CNeg)]
                                 , Map.fromAscList [(1, CNeg), (2, CPos)]
                                 , Map.fromAscList [(1, CNeg), (2, CNeg)]
                                 ]
  in assertHasSameItems expected $ clausesWithSize 2 3

test_clauseToAssertion =
  let
    x = Var $ Name "x" 0
    y = Var $ Name "y" 0
    assertions = Vector.fromList [Eq @Integer x (Num 1), Lt x (Num 1), Eq x y, Lte x y]
    clause = Map.fromList [(0, CPos), (3, CNeg)]
    expected = Or [Eq @Integer x (Num 1), Not $ Lte x y]
  in assertEqual expected $ clauseToAssertion assertions clause


------------------------------------
-- Filtering Inconsistent Clauses --
------------------------------------

test_removeInconsistentClauses_simpleAcceptPos = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] ]
  in assertHasSameItems clauses $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleAcceptNeg = let
  fv       = Vector.fromList [ Vector.fromList [False, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CNeg)] ]
  in assertHasSameItems clauses $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleAcceptMixed = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CNeg)] ]
  in assertHasSameItems clauses $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleAcceptOneMatch = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CNeg)] ]
  in assertHasSameItems clauses $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleRejectNeg = let
  fv       = Vector.fromList [ Vector.fromList [True, True, True] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CNeg)] ]
  in assertHasSameItems Vector.empty $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleRejectPos = let
  fv       = Vector.fromList [ Vector.fromList [False, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] ]
  in assertHasSameItems Vector.empty $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses_simpleRejectMixed = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False] ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CNeg), (1, CPos)] ]
  in assertHasSameItems Vector.empty $ removeInconsistentClauses clauses fv

test_removeInconsistentClauses = let
  fv       = Vector.fromList [ Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)]
                             , Map.fromAscList [(1, CNeg), (2, CPos)] -- Conflicts with 2nd FV
                             , Map.fromAscList [(1, CPos), (2, CNeg)]
                             ]
  expected = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)]
                             , Map.fromAscList [(1, CPos), (2, CNeg)]]
  in assertHasSameItems expected $ removeInconsistentClauses clauses fv


----------------------
-- Greedy Set Cover --
----------------------

test_greedySetCover = let
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] -- Only falsifies the first FV
                             , Map.fromAscList [(1, CPos), (2, CPos)] -- Falsifies the first two FVs
                             , Map.fromAscList [(0, CNeg), (1, CNeg)] -- Falsifies the last two FVs
                             ]
  fv       = Vector.fromList [ Vector.fromList [False, False, False]
                             , Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  -- Min cover is the last two clauses, which are sufficient to falsify
  -- the entire feature vector.
  expected = Vector.fromList [ Map.fromAscList [(1, CPos), (2, CPos)]
                             , Map.fromAscList [(0, CNeg), (1, CNeg)]
                             ]
  in case greedySetCover clauses fv of
       Nothing     -> assertFailure "Expected a cover"
       Just actual -> assertHasSameItems expected actual

test_greedySetCover_noCover = let
  clauses  = Vector.fromList [ Map.fromAscList [(0, CPos), (1, CPos)] -- Only falsifies the first FV
                             , Map.fromAscList [(1, CPos), (2, CPos)] -- Falsifies the first two FVs
                             ]
  fv       = Vector.fromList [ Vector.fromList [False, False, False]
                             , Vector.fromList [True, False, False]
                             , Vector.fromList [True, True,  False]
                             , Vector.fromList [True, True,  True]
                             ]
  -- No clause falsifies all feature vectors.
  in case greedySetCover clauses fv of
       Nothing     -> return () -- pass
       Just actual -> assertFailure $ "Unexpected cover: " ++ show actual



---------------------------------
-- Boolean Expression Learning --
---------------------------------

test_learnBoolExpr = let
  x        = Var $ Name "x" 0
  features = Vector.fromList [ Lt x (Num 0)
                             , Lt (Num 0) x
                             , Lt (Num 1) x
                             , Lt x (Num 5)
                             , Lt x (Num 10) ] :: Vector (Assertion Integer)
  -- Target: 0 < x < 5
  negFV    = Vector.fromList [ Vector.fromList [True,  False, False, True,  True] -- x = -1
                             , Vector.fromList [False, False, False, True,  True] -- x = 0
                             , Vector.fromList [False, True,  True,  False, True] -- x = 7
                             ]
  posFV    = Vector.fromList [ Vector.fromList [False, True,  False, True,  True] -- x = 1
                             , Vector.fromList [False, True,  True,  True,  True] -- x = 2
                             ]
  expected = And [ Lt (Num 0) x, Lt x (Num 5)]
  in do
    result <- runCeili emptyEnv $ learnBoolExpr features negFV posFV
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual

test_learnBoolExpr_largerClause = let
  x        = Var $ Name "x" 0
  features = Vector.fromList [ Lt x (Num 0)
                             , Lt (Num 0) x
                             , Lt (Num 1) x
                             , Lt x (Num 5)
                             , Lt x (Num 10)
                             , Eq x (Num 10)
                             , Eq x (Num 7)
                             ] :: Vector (Assertion Integer)
  -- Target: (x < 5  or  x >= 10  or  x = 7)  and  (x >= 0)
  negFV    = Vector.fromList [ Vector.fromList [True,  False, False, True,  True,  False, False] -- x = -1
                             , Vector.fromList [False, True,  True,  False, True,  False, False] -- x = 6
                             , Vector.fromList [False, True,  True,  False, True,  False, False] -- x = 9
                             ]
  posFV    = Vector.fromList [ Vector.fromList [False, False, False, True,  True,  False, False] -- x = 0
                             , Vector.fromList [False, True,  False, True,  True,  False, False] -- x = 1
                             , Vector.fromList [False, True,  True,  True,  True,  False, False] -- x = 2
                             , Vector.fromList [False, True,  True,  False, True,  False, True]  -- x = 7
                             , Vector.fromList [False, True,  True,  False, False, True,  False] -- x = 10
                             , Vector.fromList [False, True,  True,  False, False, False, False] -- x = 11
                             ]
  expected = And [ Or [ Lt x (Num 5)
                      , Not $ Lt x (Num 10)
                      , Eq x (Num 7)
                      ]
                 , Not $ Lt x (Num 0)
                 ]
  in do
    result <- runCeili emptyEnv $ learnBoolExpr features negFV posFV
    case result of
      Left err     -> assertFailure err
      Right actual -> assertEqual expected actual
