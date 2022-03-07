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

test_remainingGoods = do
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
  actual <- evalCI remainingGoods env
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
