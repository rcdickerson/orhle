{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CInvGenTests(htf_thisModulesTests) where
import Test.Framework
import Orhle.TestUtil

import Orhle.CInvGen

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Control.Monad.Trans.State ( evalStateT )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set


-- Test Utilities ---------------------------

state :: [(String, Integer)] -> ProgState Integer
state = Map.fromList . map (\(n, i) -> (Name n 0, i))

states :: [[(String, Integer)]] -> Set (ProgState Integer)
states = Set.fromList . (map state)

assertionFromStr :: AssertionParseable t => String -> IO (Assertion t)
assertionFromStr str =
  let assertion = parseAssertion str
  in case assertion of
    Left err -> assertFailure (show err)
    Right a  -> pure a

dummyConfig :: Configuration () (ImpProgram Integer) Integer
dummyConfig = Configuration 3 8 (\ _ -> Set.empty) (\ _ _ _ -> pure ATrue) ()

feature :: String
        -> Set (ProgState Integer)
        -> Set (ProgState Integer)
        -> IO (Feature Integer)
feature assertionStr rejected accepted = do
  assertion <- assertionFromStr assertionStr
  pure $ Feature assertion rejected accepted

clause :: Ord t => [Feature t] -> Clause t
clause features = Clause features (intersection $ map featAcceptedGoods features)

intersection :: Ord t => [Set t] -> Set t
intersection []     = Set.empty
intersection (s:[]) = s
intersection (s:ss) = foldr Set.intersection s ss

entry :: Ord t => [Feature t] -> Entry t
entry features = Entry features
                       (Set.unions $ map featRejectedBads  features)
                       (Set.unions $ map featAcceptedGoods features)

evalCeili :: Ceili a -> IO a
evalCeili task = do
  let env = mkEnv LogLevelDebug 2000 Set.empty
  mResult <- runCeili env task
  case mResult of
    Left err     -> assertFailure $ show err
    Right result -> pure result

evalCI :: CiM t a -> CIEnv t -> IO a
evalCI task env = evalCeili $ evalStateT task env

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
    assertEqual expectedBad  (envBadStates env)
    assertEqual expectedGood (envGoodStates env)

test_getRemainingGoods = do
  let state1 = state [("x", 1)]
      state2 = state [("x", 2)]
      state3 = state [("x", 3)]
      states = Set.fromList [state1, state2, state3]
  feature1 <- feature "(< x 4)" Set.empty (Set.fromList [state1, state2, state3])
  feature2 <- feature "(< x 3)" Set.empty (Set.fromList [state1, state2])
  feature3 <- feature "(< x 2)" Set.empty (Set.fromList [state1])
  let clause1 = Root (clause [feature1, feature2]) []
  let clause2 = Root (clause [feature3]) []
  let expected = Set.fromList [state3]
  let env = CIEnv Map.empty Set.empty states [clause1, clause2] Set.empty [] (\ _ -> pure ATrue) [] 8
  actual <- evalCI getRemainingGoods env
  assertEqual expected actual

test_buildCurrentResult = do
  feature1 <- feature "(< x 4)" Set.empty Set.empty
  feature2 <- feature "(< x 3)" Set.empty Set.empty
  feature3 <- feature "(< x 2)" Set.empty Set.empty
  let clause1 = Root (clause [feature1]) []
  let clause2 = Root (clause [feature2, feature3]) []
  expected <- assertionFromStr "(or (< x 4) (and (< x 3) (< x 2)))"
  let env = CIEnv Map.empty Set.empty Set.empty [clause1, clause2] Set.empty [] (\ _ -> pure ATrue) [] 8
  actual <- evalCI buildCurrentResult env
  assertEqual expected actual


-- Queue

test_qInsert = do
  feature1 <- feature "(< x 0)" (states [[("x", 4)]]) (states [[("x", -1)]])
  feature2 <- feature "(< x 1)" (states [[("x", 4)], [("x", 0)]]) (states [[("x", -1)]])
  let
    entry1      = entry [feature1]
    entry2      = entry [feature2]
    entry1Score = entryScore entry1
    entry2Score = entryScore entry2
    expected    = Map.insert entry1Score (Set.fromList [entry1])
                $ Map.insert entry2Score (Set.fromList [entry2])
                $ (Map.empty :: Queue Integer)
    actual      = qInsert entry1 $ qInsert entry2 $ qInsert entry2 $ (Map.empty :: Queue Integer)
  assertEqual expected actual

test_qPop = do
  feature1 <- feature "(< x 0)" (states [[("x", 4)]]) (states [[("x", -1)]])
  feature2 <- feature "(< x 1)" (states [[("x", 4)], [("x", 0)]]) (states [[("x", -1)]])
  let
    entry1      = entry [feature1]
    entry2      = entry [feature2]
    entry1Score = entryScore entry1
    entry2Score = entryScore entry2
    queue       = qInsert entry1 $ qInsert entry2 $ qInsert entry2 $ (Map.empty :: Queue Integer)
    expected    = if entry1Score >= entry2Score
                  then (Just entry1, qInsert entry2 Map.empty)
                  else (Just entry2, qInsert entry1 Map.empty)
    actual      = qPop queue
  assertEqual expected actual

test_qPop_empty =
  let
    queue       = Map.empty :: Queue Integer
    expected    = (Nothing, queue)
    actual      = qPop queue
  in assertEqual expected actual


-- Separator Learner

test_usefulFeatures = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodState4 = state [("x", 4)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3, goodState4]
  let badState1 = state [("y", 1)]
      badState2 = state [("y", 2)]
      badState3 = state [("y", 3)]
      badState4 = state [("y", 4)]
      badStates = Set.fromList [badState1, badState2, badState3, badState4]
  feature1 <- feature "(and (= x 1) (< y 0))" badStates (Set.fromList [goodState1])
  feature2 <- feature "(and (= x 2) (< y 0))" badStates (Set.fromList [goodState2])
  -- To start, our root clauses cover good states 1 and 2...
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = Root clause1 []
  let root2 = Root clause2 []
  -- ... and we have an entry that accepts good states 2, 3, and 4, but only rejects bad state 1.
  entryFeature <- feature "(and (> x 1) (not (= y 1)))"
                          (Set.fromList [badState1])
                          (Set.fromList [goodState2, goodState3, goodState4])
  let entry1 = Entry [entryFeature]
                     (Set.fromList [badState1])
                     (Set.fromList [goodState3, goodState4])
  -- A useful feature must keep the entry's accepted good states as a non-subset of the
  -- already accepted [feature1, feature2] while rejecting some new bad states.
  usefulFeature1 <- feature "(and (= x 3) (not (= y 2)))"
                          (Set.fromList [badState2])
                          (Set.fromList [goodState3])
  usefulFeature2 <- feature "(and (< x 5) (< y 3)))"
                          (Set.fromList [badState3, badState4])
                          goodStates
  -- This feature is not useful because it does not reject any new bad states:
  nonUsefulFeature1 <- feature "(and (< x 5) (not (= y 1)))"
                               (Set.fromList [badState1])
                               goodStates
  -- This feature is not useful because it does not overlap any of the entry's accepted
  -- good states:
  nonUsefulFeature2 <- feature "(and (= x 1) (> y 5))"
                                badStates
                                (Set.fromList [goodState1])
  -- This feature is not useful because, while it does overlap the entry's accepted
  -- good states, it takes the set of accepted good states to a subset of states
  -- already accepted by the root clauses.
  nonUsefulFeature3 <- feature "(and (= x 2) (> y 5))"
                                badStates
                                (Set.fromList [goodState2])
  let features = Set.fromList [ feature1
                              , feature2
                              , entryFeature
                              , usefulFeature1
                              , usefulFeature2
                              , nonUsefulFeature1
                              , nonUsefulFeature2
                              , nonUsefulFeature3
                              ]
  let expected = [usefulFeature1, usefulFeature2]
  let env = CIEnv Map.empty badStates goodStates [root1, root2] features [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (usefulFeatures entry1) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_learnSeparator_returnsTrueWhenNoBads =
  let
    badStates = Set.empty
    goodStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalCI learnSeparator env
    assertEqual (Just ATrue) sep

test_learnSeparator_returnsFalseWhenNoGoods =
  let
    badStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    goodStates = Set.empty
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalCI learnSeparator env
    assertEqual (Just AFalse) sep

test_learnSeparator_returnsTrueWhenNoBadsOrGoods =
  let
    badStates = Set.empty
    goodStates = Set.empty
    env = mkCIEnv dummyConfig (Job badStates goodStates ATrue impSkip ATrue)
  in do
    sep <- evalCI learnSeparator env
    assertEqual (Just ATrue) sep
