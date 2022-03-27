{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CInvGenTests(htf_thisModulesTests) where
import Test.Framework
import Orhle.TestUtil
import Debug.Trace

import Orhle.CInvGen

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Control.Monad.Trans.State ( evalStateT, runStateT )
import qualified Data.Map as Map
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import Data.Set ( Set )
import qualified Data.Set as Set


-- Test Utilities ---------------------------

state :: [(String, Integer)] -> ProgState Integer
state = Map.fromList . map (\(n, i) -> (Name n 0, i))

bstate :: Int -> [(String, Integer)] -> BadState Integer
bstate stateId = BadState stateId . state

gstate :: Int -> [(String, Integer)] -> GoodState Integer
gstate stateId = GoodState stateId . state

states :: [[(String, Integer)]] -> Set (ProgState Integer)
states = Set.fromList . map state

bstates :: [(Int, [(String, Integer)])] -> Set (BadState Integer)
bstates = Set.fromList . (map $ uncurry bstate)

gstates :: [(Int, [(String, Integer)])] -> Set (GoodState Integer)
gstates = Set.fromList . (map $ uncurry gstate)

dummyConfig :: Configuration () (ImpProgram Integer) Integer
dummyConfig = Configuration 3 8 (\ _ -> Set.empty) (\ _ _ _ -> pure ATrue) ()

feature :: Int
        -> String
        -> IntSet
        -> IO (Feature Integer)
feature featureId assertionStr accepted = do
  assertion <- assertionFromStr assertionStr
  pure $ Feature featureId assertion accepted

clause :: Ord t => [Feature t] -> Clause t
clause features =
  let
    featureIds = IntSet.fromList $ map featId features
  in Clause featureIds (intersection $ map featAcceptedGoods features)

intersection :: [IntSet] -> IntSet
intersection []     = IntSet.empty
intersection (s:[]) = s
intersection (s:ss) = foldr IntSet.intersection s ss

entry :: Ord t => [Feature t] -> IntSet -> Entry t
entry features rejectedBads =
  Entry (IntSet.fromList $ map featId features)
        rejectedBads
        (IntSet.unions $ map featAcceptedGoods features)

evalC :: CiM t a -> CIEnv t -> IO a
evalC task env = evalCeili Set.empty $ evalStateT task env

runC :: CiM t a -> CIEnv t -> IO (CIEnv t)
runC task env = do
  (a, env) <- evalCeili Set.empty $ runStateT task env
  pure env

---------------------------------------------


-- Utility

test_closeNames =
  let
    names    = [Name "a" 0, Name "b" 0, Name "c" 0, Name "d" 0]
    expected = state [("a", 12), ("b", 4), ("c", 0), ("d", 0)]
    actual   = closeNames names $ state [("a", 12), ("b", 4)]
  in assertEqual expected actual

test_mkCIEnv_closesStateNames =
  let
    badStates = Set.fromList [ state[("x", 2)]
                             , state[("y", 0), ("z", 10)]
                             ]
    goodStates = Set.fromList [ state[("a", 12), ("b", 4)]
                              , state[("c", 4)]
                              , state[("d", 8)]
                              ]
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
    expectedBad = Set.fromList [ state[ ("a", 0), ("b", 0), ("c", 0), ("d", 0)
                                      , ("x", 2), ("y", 0), ("z", 0)]
                               , state[ ("a", 0), ("b", 0), ("c", 0), ("d", 0)
                                      , ("x", 0), ("y", 0), ("z", 10)]
                               ]
    expectedGood = Set.fromList [ state[ ("a", 12), ("b", 4), ("c", 0), ("d", 0)
                                       , ("x", 0), ("y", 0), ("z", 0)]
                                , state[ ("a", 0), ("b", 0), ("c", 4), ("d", 0)
                                       , ("x", 0), ("y", 0), ("z", 0)]
                                , state[ ("a", 0), ("b", 0), ("c", 0), ("d", 8)
                                       , ("x", 0), ("y", 0), ("z", 0)]
                                ]
  in do
    assertEqual expectedBad  (Set.map bsState . stBadStates  . envStates $ env)
    assertEqual expectedGood (Set.map gsState . stGoodStates . envStates $ env)

test_putRootsAndGetRemainingGoods = do
  let state1 = gstate 1 [("x", 1)]
      state2 = gstate 2 [("x", 2)]
      state3 = gstate 3 [("x", 3)]
      goods  = Set.fromList [state1, state2, state3]
  feature1 <- feature 1 "(< x 4)" (IntSet.fromList [1, 2, 3])
  feature2 <- feature 2 "(< x 3)" (IntSet.fromList [1, 2])
  feature3 <- feature 3 "(< x 2)" (IntSet.fromList [1])
  let fc = fcAddFeature feature1 IntSet.empty
         $ fcAddFeature feature2 IntSet.empty
         $ fcAddFeature feature3 IntSet.empty
         $ fcEmpty
  let clause1 = RootClause (clause [feature1, feature2]) []
  let clause2 = RootClause (clause [feature3]) []
  let expected = IntSet.fromList [3]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goods
                  , envRootClauses       = []
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let task = do
        putRootClauses [clause1, clause2]
        getRemainingGoods
  actual <- evalC task env
  assertEqual expected actual

test_buildCurrentResult = do
  feature1 <- feature 1 "(< x 4)" IntSet.empty
  feature2 <- feature 2 "(< x 3)" IntSet.empty
  feature3 <- feature 3 "(< x 2)" IntSet.empty
  let clause1 = RootClause (clause [feature1]) []
  let clause2 = RootClause (clause [feature2, feature3]) []
  let fc = fcAddFeature feature1 IntSet.empty
         $ fcAddFeature feature2 IntSet.empty
         $ fcAddFeature feature3 IntSet.empty
         $ fcEmpty
  expected <- assertionFromStr "(or (< x 4) (and (< x 3) (< x 2)))"
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty Set.empty
                  , envRootClauses       = [clause1, clause2]
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  actual <- evalC buildCurrentResult env
  assertEqual expected actual


-- Queue

test_qInsert = do
  feature1 <- feature 1 "(< x 0)" $ IntSet.fromList [0]
  let feature1Rejected = IntSet.fromList [0]

  feature2 <- feature 2 "(< x 1)" $ IntSet.fromList [0]
  let feature2Rejected = IntSet.fromList [0, 1]

  let
    entry1      = entry [feature1] feature1Rejected
    entry2      = entry [feature2] feature2Rejected
    entry1Score = entryScore entry1
    entry2Score = entryScore entry2
    expected    = Map.insert entry1Score (Set.fromList [entry1])
                $ Map.insert entry2Score (Set.fromList [entry2])
                $ Map.empty
    actual      = qInsert entry1 $ qInsert entry2 $ qInsert entry2 $ (qEmpty :: Queue Integer)
  assertEqual expected (qQueue actual)

test_qPop = do
  feature1 <- feature 1 "(< x 0)" $ IntSet.fromList [0]
  let feature1Rejected = IntSet.fromList [0]

  feature2 <- feature 2 "(< x 1)" $ IntSet.fromList [0]
  let feature2Rejected = IntSet.fromList [0, 1]

  let
    entry1      = entry [feature1] feature1Rejected
    entry2      = entry [feature2] feature2Rejected
    entry1Score = entryScore entry1
    entry2Score = entryScore entry2
    queue       = qInsert entry1 $ qInsert entry2 $ qInsert entry2 $ (qEmpty :: Queue Integer)
    (expectedEntry, expectedQueue) = if entry1Score >= entry2Score
                                     then (Just entry1, qQueue $ qInsert entry2 qEmpty)
                                     else (Just entry2, qQueue $ qInsert entry1 qEmpty)
    (actualEntry, actualQueue) = qPop queue
  assertEqual expectedEntry actualEntry
  assertEqual expectedQueue (qQueue actualQueue)

test_qPop_empty =
  let
    queue       = qEmpty :: Queue Integer
    expected    = (Nothing, queue)
    actual      = qPop queue
  in assertEqual expected actual


-- Separator Learner

test_usefulFeatures = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodState4 = gstate 4 [("x", 4)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3, goodState4]
  let badState1 = bstate 1 [("y", 1)]
      badState2 = bstate 2 [("y", 2)]
      badState3 = bstate 3 [("y", 3)]
      badState4 = bstate 4 [("y", 4)]
      badStates = Set.fromList [badState1, badState2, badState3, badState4]
  -- To start, our root clauses cover good states 1 and 2...
  feature1 <- feature 1 "(and (= x 1) (< y 0))" $ IntSet.fromList [1]
  feature2 <- feature 2 "(and (= x 2) (< y 0))" $ IntSet.fromList [2]
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
  let clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- ... and we have an entry that accepts good states 2, 3, and 4, but only rejects bad state 1.
  entryFeature3 <- feature 3 "(and (> x 1) (not (= y 1)))" $ IntSet.fromList [2, 3, 4]
  let entry1 = Entry (IntSet.fromList [3])
                     (IntSet.fromList [1])
                     (IntSet.fromList [3, 4])
  -- A useful feature must keep the entry's accepted good states as a non-subset of the
  -- already accepted [feature1, feature2] while rejecting some new bad states.
  usefulFeature4 <- feature 4 "(and (= x 3) (not (= y 2)))" $ IntSet.fromList [3]
  usefulFeature5 <- feature 5 "(and (< x 5) (< y 3)))" $ IntSet.fromList [1, 2, 3, 4]
  -- This feature is not useful because it does not reject any new bad states:
  nonUsefulFeature6 <- feature 6 "(and (< x 5) (not (= y 1)))" $ IntSet.fromList [1, 2, 3, 4]
  -- This feature is not useful because it does not overlap any of the entry's accepted
  -- good states:
  nonUsefulFeature7 <- feature 7 "(and (= x 1) (> y 5))" (IntSet.fromList [1])
  -- This feature is not useful because, while it does overlap the entry's accepted
  -- good states, it takes the set of accepted good states to a subset of states
  -- already accepted by the root clauses.
  nonUsefulFeature8 <- feature 8 "(and (= x 2) (> y 5))" (IntSet.fromList [2])

  let fc = fcAddFeature feature1 (IntSet.fromList [1, 2, 3, 4])
         $ fcAddFeature feature2 (IntSet.fromList [1, 2, 3, 4])
         $ fcAddFeature entryFeature3 (IntSet.singleton 1)
         $ fcAddFeature usefulFeature4 (IntSet.fromList [2])
         $ fcAddFeature usefulFeature5 (IntSet.fromList [3, 4])
         $ fcAddFeature nonUsefulFeature6 (IntSet.fromList [1])
         $ fcAddFeature nonUsefulFeature7 (IntSet.fromList [1, 2, 3, 4])
         $ fcAddFeature nonUsefulFeature8 (IntSet.fromList [1, 2, 3, 4])
         $ fcEmpty
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates badStates goodStates
                  , envRootClauses       = [root1, root2]
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let expected = [4, 5]
  actual <- evalC (usefulFeatures entry1) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_learnSeparator_returnsTrueWhenNoBads =
  let
    badStates = Set.empty
    goodStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalC learnSeparator env
    assertEqual (Just (ATrue, [])) sep

test_learnSeparator_returnsFalseWhenNoGoods =
  let
    badStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    goodStates = Set.empty
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalC learnSeparator env
    assertEqual (Just (AFalse, [])) sep

test_learnSeparator_returnsTrueWhenNoBadsOrGoods =
  let
    badStates = Set.empty
    goodStates = Set.empty
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalC learnSeparator env
    assertEqual (Just (ATrue, [])) sep


-- RootClause Clause Update

test_addRootClause_noCover = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature 1 "(= x 1)" (IntSet.fromList [1])
  feature2 <- feature 2 "(= x 2)" (IntSet.fromList [2])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
  let clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers good state 3.
  newFeature <- feature 3 "(= x 3)" (IntSet.fromList [3])
  let newClause = Clause (IntSet.fromList [3]) (IntSet.fromList [3])
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = [root1, root2]
                  , envRootsAccepted     = IntSet.fromList [1, 2]
                  , envFeatureCache      = fcAddFeature feature1 IntSet.empty
                                         $ fcAddFeature feature2 IntSet.empty
                                         $ fcAddFeature newFeature IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  -- Our new clause list should include all three root clauses (the two original plus one new).
  let expected = [root1, root2, RootClause newClause []]
  actual <- evalC (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_singleCover = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature 1 "(= x 1)" (IntSet.fromList [1])
  feature2 <- feature 2 "(= x 2)" (IntSet.fromList [2])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
  let clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers good states 2 and 3.
  newFeature <- feature 3 "(> x 1)" (IntSet.fromList [2, 3])
  let newClause = Clause (IntSet.fromList [3]) (IntSet.fromList [2, 3])
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = [root1, root2]
                  , envRootsAccepted     = IntSet.fromList [1, 2]
                  , envFeatureCache      = fcAddFeature feature1 IntSet.empty
                                         $ fcAddFeature feature2 IntSet.empty
                                         $ fcAddFeature newFeature IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  -- Our new clause list should include the first root, plus the new clause covering
  -- the second original root.
  let expected = [root1, RootClause newClause [root2]]
  actual <- evalC (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_multiCover = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature 1 "(= x 1)" (IntSet.fromList [1])
  feature2 <- feature 2 "(= x 2)" (IntSet.fromList [2])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
  let clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers all good states.
  newFeature <- feature 3 "(< x 4)" $ IntSet.fromList [1, 2, 3]
  let newClause = Clause (IntSet.fromList [3]) $ IntSet.fromList [1, 2, 3]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = [root1, root2]
                  , envRootsAccepted     = IntSet.fromList [1, 2]
                  , envFeatureCache      = fcAddFeature feature1 IntSet.empty
                                         $ fcAddFeature feature2 IntSet.empty
                                         $ fcAddFeature newFeature IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  -- Our new clause list should include only the new clause, covering both original roots.
  let expected = [RootClause newClause [root1, root2]]
  actual <- evalC (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_exactCover = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature 1 "(= x 1)" (IntSet.fromList [1])
  feature2 <- feature 2 "(= x 2)" (IntSet.fromList [2])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
  let clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that also covers good states 1 and 2.
  newFeature <- feature 3 "(or (= x 1) (= x 2))" (IntSet.fromList [1, 2])
  let newClause = Clause (IntSet.fromList [3]) (IntSet.fromList [1, 2])
  let fc = fcAddFeature feature1   IntSet.empty
         $ fcAddFeature feature2   IntSet.empty
         $ fcAddFeature newFeature IntSet.empty
         $ fcEmpty
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = [root1, root2]
                  , envRootsAccepted     = IntSet.fromList [1, 2]
                  , envFeatureCache      = fcAddFeature feature1 IntSet.empty
                                         $ fcAddFeature feature2 IntSet.empty
                                         $ fcAddFeature newFeature IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  -- The root clause list should now be the new clause covering the two previous clauses.
  let expected = [RootClause newClause [root1, root2]]
  actual <- evalC (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_ignoresDuplicateAssertions = do
  let goodState0 = gstate 0 [("x", 0)]
      goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodStates = Set.fromList [goodState1, goodState2]
  feature1 <- feature 1 "(< x 3)" (IntSet.fromList[1, 2])
  feature2 <- feature 2 "(< x 2)" (IntSet.fromList [0, 1])
  feature3 <- feature 3 "(< x 1)" (IntSet.fromList [0])
  let rclause   = clause [feature1, feature2]
  let covered   = clause [feature3]
  let root      = RootClause rclause [RootClause covered []]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = [root]
                  , envRootsAccepted     = IntSet.fromList[1, 2]
                  , envFeatureCache      = fcAddFeature feature1 IntSet.empty
                                         $ fcAddFeature feature2 IntSet.empty
                                         $ fcAddFeature feature3 IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  -- Adding a clause with the same set of features should have no effect.
  let duplicate = clause [feature2, feature1]
  let expected = [root]
  actual <- evalC (addRootClause duplicate >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_deepInsert = do
  let goodState1 = gstate 1 [("x", 1)]
      goodState2 = gstate 2 [("x", 2)]
      goodState3 = gstate 3 [("x", 3)]
      goodState4 = gstate 4 [("x", 4)]
      goodState5 = gstate 5 [("x", 5)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3, goodState4, goodState5]
  -- To start, our root clauses form a linear chain of inclusions:
  --   root4 <--- root3 <--- root2 <--- root1
  feature1 <- feature 1 "(<= x 5)" (IntSet.fromList [5])
  feature2 <- feature 2 "(<= x 3)" (IntSet.fromList [3, 4, 5])
  feature3 <- feature 3 "(<= x 2)" (IntSet.fromList [2, 3, 4, 5])
  feature4 <- feature 4 "(<= x 1)" (IntSet.fromList [1, 2, 3, 4, 5])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [5])
      clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [3, 4, 5])
      clause3 = Clause (IntSet.fromList [3]) (IntSet.fromList [2, 3, 4, 5])
      clause4 = Clause (IntSet.fromList [4]) (IntSet.fromList [1, 2, 3, 4, 5])
  let root1 = RootClause clause1 []
      root2 = RootClause clause2 [root1]
      root3 = RootClause clause3 [root2]
      root4 = RootClause clause4 [root3]
      roots = [root4]
  -- Add a clause that needs to be inserted between root2 and root1
  --   root4 <--- root3 <--- root2 <--- *newClause* <--- root1
  newFeature <- feature 5 "(<= x 4)" (IntSet.fromList [4, 5])
  let newClause = Clause (IntSet.fromList [5]) (IntSet.fromList [4, 5])
  let root1'  = RootClause clause1 []
      newRoot = RootClause newClause [root1']
      root2'  = RootClause clause2 [newRoot]
      root3'  = RootClause clause3 [root2']
      root4'  = RootClause clause4 [root3']
      expected = [root4']
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates Set.empty goodStates
                  , envRootClauses       = roots
                  , envRootsAccepted     = IntSet.fromList [3]
                  , envFeatureCache      = fcAddFeature feature1   IntSet.empty
                                         $ fcAddFeature feature2   IntSet.empty
                                         $ fcAddFeature feature3   IntSet.empty
                                         $ fcAddFeature feature4   IntSet.empty
                                         $ fcAddFeature newFeature IntSet.empty
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  actual <- evalC (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)


-- Counterexample Update

test_tagFeature_accepts = do
  let badStates  = bstates [(0, [("x", 1)])]
  let goodStates = gstates [(0, [("x", -1)])]
  feature1 <- feature 1 "(< x 0)" $ IntSet.fromList [0]
  let fc = fcAddFeature feature1 (IntSet.fromList [0])
         $ fcEmpty
  let newBadState = bstate 1 [("x", -2)]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates (Set.insert newBadState badStates) goodStates
                  , envRootClauses       = []
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let expected = (feature1, Accepts)
  actual <- evalC (tagFeature newBadState feature1) env
  assertEqual expected actual

test_tagFeature_rejects = do
  let badStates  = bstates [(0, [("x", 1)])]
  let goodStates = gstates [(0, [("x", -1)])]
  feature1 <- feature 1 "(< x 0)" $ IntSet.fromList [0]
  let fc = fcAddFeature feature1 (IntSet.fromList [0])
         $ fcEmpty
  let newBadState = bstate 1 [("x", 2)]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates (Set.insert newBadState badStates) goodStates
                  , envRootClauses       = []
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let expected = (feature1, Rejects)
  actual <- evalC (tagFeature newBadState feature1) env
  assertEqual expected actual

test_updateQueue = do
  let bads  = bstates [ (0, [("x", 0)])
                      , (1, [("x", 1)])
                      , (3, [("x", 3)])]
  let goods = gstates [ (0, [("x", 10)])]
  feature1 <- feature 1 "(> x 1)" $ IntSet.fromList [0]
  feature2 <- feature 2 "(> x 3)" $ IntSet.fromList [0]
  feature3 <- feature 3 "(> x 4)" $ IntSet.fromList [0]
  let queue = qInsert (Entry (IntSet.fromList [1])    (IntSet.fromList [0])       (IntSet.fromList [0]))
            $ qInsert (Entry (IntSet.fromList [2])    (IntSet.fromList [0, 1, 3]) (IntSet.fromList [0]))
            $ qInsert (Entry (IntSet.fromList [3])    (IntSet.fromList [0, 1, 3]) (IntSet.fromList [0]))
            $ qInsert (Entry (IntSet.fromList [1, 2]) (IntSet.fromList [0, 1, 3]) (IntSet.fromList [0]))
            $ qEmpty
  let newBadState = bstate 2 [("x", 2)]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates (Set.insert newBadState bads) goods
                  , envRootClauses       = []
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fcAddFeature feature1 (IntSet.fromList [0])
                                         $ fcAddFeature feature2 (IntSet.fromList [0, 1, 2, 3])
                                         $ fcAddFeature feature3 (IntSet.fromList [0, 1, 2, 3])
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let expected = qInsert (Entry (IntSet.fromList [1])    (IntSet.fromList [0])          (IntSet.fromList [0]))
               $ qInsert (Entry (IntSet.fromList [2])    (IntSet.fromList [0, 1, 2, 3]) (IntSet.fromList [0]))
               $ qInsert (Entry (IntSet.fromList [3])    (IntSet.fromList [0, 1, 2, 3]) (IntSet.fromList [0]))
               $ qInsert (Entry (IntSet.fromList [1, 2]) (IntSet.fromList [0, 1, 2, 3]) (IntSet.fromList [0]))
               $ qEmpty
  actual <- evalC (updateQueue newBadState queue) env
  assertEqual expected actual

test_addNewlyUsefulCandidates = do
  assertion1 <- assertionFromStr "(< x 1)" -- Rejects all goods, eliminated when we look
                                           -- at it for rejecting some bad state (but not
                                           -- sooner).
  assertion2 <- assertionFromStr "(< x 2)" -- Rejects new bad while accepting goods.
  assertion3 <- assertionFromStr "(< x 3)" -- Does not reject new bad.
  assertion4 <- assertionFromStr "(< x 4)" -- Does not reject new bad.
  let candidates = [assertion1, assertion2, assertion3, assertion4]
  let goodStates   = gstates [(0, [("x", 1)])]
  let oldBadStates = bstates [(0, [("x", 0)])]
  let newBadState  = bstate 1 [("x", 2)]
  let newBadStates = Set.insert newBadState oldBadStates
  expectedFeature <- feature 1 "(< x 2)" (IntSet.fromList [0])
  let expectedQueue       = qInsert (Entry (IntSet.fromList [1]) (IntSet.fromList [1]) (IntSet.fromList [0]))
                          $ qEmpty
  let expectedCandidates' = [assertion3, assertion4]
  let expectedFeatures'   = [expectedFeature]
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates newBadStates goodStates
                  , envRootClauses       = []
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fcEmpty
                  , envFeatureCandidates = candidates
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  let task = do
        addNewlyUsefulCandidates newBadState
        queue <- getQueue
        fCandidates <- getFeatureCandidates
        features <- getFeatures
        pure (queue, fCandidates, features)
  (actualQueue, actualCandidates', actualFeatures') <- evalC task env
  assertEqual expectedQueue       actualQueue
  assertEqual expectedCandidates' actualCandidates'
  assertEqual expectedFeatures'   actualFeatures'

test_updateRootClauses = do
  -- Dummy good states: assertions don't actually have to accept them
  -- to make the test setup work.
  let goodState1    = gstate 1 [("a", 1)]
      goodState2    = gstate 2 [("a", 2)]
      goodState3    = gstate 3 [("a", 3)]
      goodState4    = gstate 4 [("a", 4)]
      goodState5    = gstate 5 [("a", 5)]
      goodStates    = Set.fromList [goodState1, goodState2, goodState3, goodState4, goodState5]
  let badState1     = bstate 1 [("x", 1), ("y", 1), ("z", 1)]
      origBadStates = Set.fromList [badState1]
  --
  -- To start, root list is [root1, root6] with coverage as follows:
  --
  --    root1
  --
  --      x             x
  --    root6 <------ root4 <---- root2
  --             |
  --             +--- root5 <---- root3
  --
  -- We will later introduce a counterexample which destroys root6 and root4.
  --
  let assertion1 = "(and (= x 0) (=  y 1) (=  z 1))"
      assertion2 = "(and (= x 1) (=  y 0) (=  z 1))"
      assertion3 = "(and (= x 1) (=  y 1) (=  z 0))"
      assertion4 = "(and (= x 1) (<= y 0) (=  z 1))"
      assertion5 = "(and (= x 1) (=  y 1) (<= z 0))"
      assertion6 = "(and (= x 1) (<= y 0) (<= z 1))"
  feature1 <- feature 1 assertion1 (IntSet.fromList [ 1 ])
  feature2 <- feature 2 assertion2 (IntSet.fromList [ 2 ])
  feature3 <- feature 3 assertion3 (IntSet.fromList [ 3 ])
  feature4 <- feature 4 assertion4 (IntSet.fromList [ 2, 4 ])
  feature5 <- feature 5 assertion5 (IntSet.fromList [ 3, 5 ])
  feature6 <- feature 6 assertion6 (IntSet.fromList [ 2, 3, 4, 5 ])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1])
      clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [2])
      clause3 = Clause (IntSet.fromList [3]) (IntSet.fromList [3])
      clause4 = Clause (IntSet.fromList [4]) (IntSet.fromList [2, 4])
      clause5 = Clause (IntSet.fromList [5]) (IntSet.fromList [3, 5])
      clause6 = Clause (IntSet.fromList [6]) (IntSet.fromList [2, 3, 4, 5])
  let root1 = RootClause clause1 []
      root2 = RootClause clause2 []
      root3 = RootClause clause3 []
      root4 = RootClause clause4 [root2]
      root5 = RootClause clause5 [root3]
      root6 = RootClause clause6 [root4, root5]
      origRootList = [root1, root6]
  --
  -- A counterexample which kills root6 and root4 (i.e., roots 6 and 4 accept the new bad state):
  --
  let newBadState  = bstate 2 [("x", 1), ("y", -1), ("z", 1)]
      newBadStates = Set.insert newBadState origBadStates
  --
  -- After update, the root list should be [root1, root2, root5],
  -- with root5 still covering root3:
  --
  --    root1
  --
  --    root2
  --
  --    root5 <---- root3
  --
  let root1' = RootClause clause1 []
      root2' = RootClause clause2 []
      root3' = RootClause clause3 []
      root5' = RootClause clause5 [root3']
      expected = [root1', root2', root5']
  let fc = fcAddFeature feature1 (IntSet.fromList [2])
         $ fcAddFeature feature2 (IntSet.fromList [2])
         $ fcAddFeature feature3 (IntSet.fromList [2])
         $ fcAddFeature feature4 (IntSet.fromList [1])
         $ fcAddFeature feature5 (IntSet.fromList [2])
         $ fcAddFeature feature6 (IntSet.fromList [1])
         $ fcEmpty
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates newBadStates goodStates
                  , envRootClauses       = origRootList
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fc
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  actual <- evalC (updateRootClauses newBadState origRootList) env
  assertEqual expected actual

test_updateRootClauses_combinesCoverage = do
  -- Dummy good states: assertions don't actually have to accept them
  -- to make the test setup work.
  let goodState1    = gstate 1 [("a", 1)]
      goodState2    = gstate 2 [("a", 2)]
      goodStates    = Set.fromList [goodState1, goodState2]
  let badState1     = bstate 1 [("x", 10)]
      origBadStates = Set.fromList [badState1]
  --
  -- To start, root list is [root1] with coverage as follows:
  --
  --    root1 <------ root2
  --             |
  --             +--- root3
  --
  -- where root2 would also cover root3.
  --
  feature1 <- feature 1 "(< x 5)" (IntSet.fromList [1, 2])
  feature2 <- feature 2 "(< x 4)" (IntSet.fromList [1, 2])
  feature3 <- feature 3 "(= x 3)" (IntSet.fromList [1])
  let clause1 = Clause (IntSet.fromList [1]) (IntSet.fromList [1, 2])
      clause2 = Clause (IntSet.fromList [2]) (IntSet.fromList [1, 2])
      clause3 = Clause (IntSet.fromList [3]) (IntSet.fromList [1])
  let root2 = RootClause clause2 []
      root3 = RootClause clause3 []
      root1 = RootClause clause1 [root2, root3]
      origRootList = [root1]
  --
  -- A counterexample which kills root1.
  --
  let newBadState  = bstate 2 [("x", 4)]
      newBadStates = Set.insert newBadState origBadStates
  let clause2' = Clause (IntSet.fromList [2]) (IntSet.fromList [1, 2])
      clause3' = Clause (IntSet.fromList [3]) (IntSet.fromList [1])
  --
  -- After update, the root list should be [root2] with root2 now covering root3:
  --
  --    root2 <---- root3
  --
  let root3' = RootClause clause3' []
      root2' = RootClause clause2' [root3']
      expected = [root2']
  let env = CIEnv { envQueue             = qEmpty
                  , envStates            = mkStates newBadStates goodStates
                  , envRootClauses       = origRootList
                  , envRootsAccepted     = IntSet.empty
                  , envFeatureCache      = fcAddFeature feature1 (IntSet.fromList [1])
                                         $ fcAddFeature feature2 (IntSet.fromList [2])
                                         $ fcAddFeature feature3 (IntSet.fromList [2])
                                         $ fcEmpty
                  , envFeatureCandidates = []
                  , envGoalQuery         = (\ _ -> pure ATrue)
                  , envStateNames        = []
                  , envMaxClauseSize     = 8
                  }
  actual <- evalC (updateRootClauses newBadState origRootList) env
  assertEqual expected actual

-- CVInvGen (end-to-end test of invariant inference).

test_cvInvGen = do
  -- Target invariant: x <= y /\ y <= x
  let x = Name "x" 0
  let y = Name "y" 0
  features <- sequence $ [ assertionFromStr "(<= x 0)"
                         , assertionFromStr "(<= y 0)"
                         , assertionFromStr "(<= x 10)"
                         , assertionFromStr "(<= y 10)"
                         , assertionFromStr "(<= x y)"
                         , assertionFromStr "(<= y x)"
                         ] :: IO [Assertion Integer]
  loopCond <- assertionFromStr "(and (< x 10) (< y 10))"
  let loopBody = impSeq [ impAsgn x (AAdd (AVar x) (ALit 1))
                        , impAsgn y (AAdd (AVar y) (ALit 1))
                        ] :: ImpProgram Integer
  let goodStates = states [ [("x", 0), ("y", 0)]
                          , [("x", 1), ("y", 1)]
                          , [("x", 2), ("y", 2)]
                          ]
  postCond <- assertionFromStr "(= x y)"
  let cfg = Configuration 2 12 (\_ -> Set.fromList features) impBackwardPT
          $ ImpPieContext Map.empty (Set.fromList [x, y]) (Set.singleton (10 :: Integer))
  let job = Job Set.empty goodStates loopCond loopBody postCond
  expected <- assertionFromStr "(and (<= x y) (<= y x))"
  mActual  <- evalCeili Set.empty $ cInvGen cfg job
  case mActual of
    Nothing     -> assertFailure "Unable to find separator."
    Just actual -> assertEquivalent expected actual
