{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CVInvGenTests(htf_thisModulesTests) where
import Test.Framework
import Orhle.TestUtil

import Orhle.CVInvGen

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

feature :: String
        -> Set (ProgState Integer)
        -> Set (ProgState Integer)
        -> IO (Feature Integer)
feature assertionStr rejected accepted = do
  assertion <- assertionFromStr assertionStr
  pure $ Feature assertion rejected accepted

dummyWp :: WeakestPre () (ImpProgram t) Integer
dummyWp = WeakestPre (\ _ _ _ -> pure ATrue) ()

evalCeili :: Ceili a -> IO a
evalCeili task = do
  mResult <- runCeili (defaultEnv Set.empty) task
  case mResult of
    Left err     -> assertFailure $ show err
    Right result -> pure result

evalCvi :: CviM t a -> CviEnv t -> IO a
evalCvi task env = evalCeili $ evalStateT task env


---------------------------------------------


-- Close Names

test_closeNames =
  let
    names    = [Name "a" 0, Name "b" 0, Name "c" 0, Name "d" 0]
    expected = state [("a", 12), ("b", 4), ("c", 0), ("d", 0)]
    actual   = closeNames names $ state [("a", 12), ("b", 4)]
  in assertEqual expected actual

test_mkCviEnv_closesStateNames =
  let
    badStates = Set.fromList [ state[("x", 2)]
                             , state[("y", 0), ("z", 10)]
                             ]
    goodStates = Set.fromList [ state[("a", 12), ("b", 4)]
                              , state[("c", 4)]
                              , state[("d", 8)]
                              ]
    env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
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


-- Queue

test_qInsert = do
  feature1 <- feature "(< x 0)" (states [[("x", 4)]]) (states [[("x", -1)]])
  feature2 <- feature "(< x 1)" (states [[("x", 4)], [("x", 0)]]) (states [[("x", -1)]])
  let
    entry1      = Entry [] [feature1] False
    entry2      = Entry [[feature2]] [] False
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
    entry1      = Entry [] [feature1] False
    entry2      = Entry [[feature2]] [] False
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


-- Conversions

test_assertionToFeature = do
  assertion <- assertionFromStr "(> x 1)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", -10)]
                          , [("x",  10)]
                          ]
  let expected = Feature assertion (states [[("x", 0)], [("x", 1)]])
                                   (states [[("x", 10)]])
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  actual <- evalCvi (assertionToFeature assertion) env
  assertEqual expected actual

test_featureToEntry_rejectsAllBads_acceptsNoGoods = do
  assertion <- assertionFromStr "(> x 5)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", -20)]
                          , [("x", -10)]
                          ]
  let feature1 = Feature assertion badStates Set.empty
  let expected = Entry [[feature1]] [] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (featureToEntry feature1) env
  assertEqual expected entry

test_featureToEntry_rejectsAllBads_acceptsSomeGoods = do
  assertion <- assertionFromStr "(> x 5)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x",  10)]
                          , [("x", -10)]
                          ]
  let feature1 = Feature assertion badStates $ Set.singleton (state [("x", 10)])
  let expected = Entry [[feature1]] [] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (featureToEntry feature1) env
  assertEqual expected entry

test_featureToEntry_rejectsAllBads_acceptsAllGoods = do
  assertion <- assertionFromStr "(> x 5)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", 10)]
                          , [("x", 20)]
                          ]
  let feature1 = Feature assertion badStates goodStates
  let expected = Entry [[feature1]] [] True
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (featureToEntry feature1) env
  assertEqual expected entry

test_featureToEntry_rejectsSomeBads_acceptsSomeGoods = do
  assertion <- assertionFromStr "(> x 1)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", -10)]
                          , [("x",  10)]
                          ]
  let feature1 = Feature assertion (states [[("x", 0)], [("x", 1)]]) (states [[("x", 10)]])
  let expected = Entry [] [feature1] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (featureToEntry feature1) env
  assertEqual expected entry

test_featureToEntry_rejectsSomeBads_acceptsAllGoods = do
  assertion <- assertionFromStr "(> x 1)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", 10)]
                          , [("x", 20)]
                          ]
  let feature1 = Feature assertion (states [[("x", 0)], [("x", 1)]]) goodStates
  let expected = Entry [] [feature1] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (featureToEntry feature1) env
  assertEqual expected entry

test_entryToAssertion = do
  feature1 <- feature "(< x 0)" Set.empty Set.empty
  feature2 <- feature "(= y 3)" Set.empty Set.empty
  feature3 <- feature "(> z 2)" Set.empty Set.empty
  let entry = Entry [ [feature1, feature2], [feature3] ] [] True
  expected <- assertionFromStr "(or (and (< x 0) (= y 3)) (> z 2))"
  let actual = entryToAssertion entry
  assertEqual expected actual

test_assertionToEntry = do
  assertion <- assertionFromStr "(> x 1)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          , [("x", 2)]
                          ]
  let goodStates = states [ [("x", -10)]
                          , [("x",  10)]
                          ]
  let feature = Feature assertion (states [[("x", 0)], [("x", 1)]])
                                  (states [[("x", 10)]])
  let expected = Entry [] [feature] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  entry <- evalCvi (assertionToEntry assertion) env
  assertEqual expected entry


-- Utility

test_acceptsAllGoods_true = do
  assertion1 <- assertionFromStr "(= x 10)"
  assertion2 <- assertionFromStr "(< x 25)"
  assertion3 <- assertionFromStr "(> x 15)"
  assertion4 <- assertionFromStr "(= x 30)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          ]
  let goodStates = states [ [("x", 10)]
                          , [("x", 20)]
                          , [("x", 30)]
                          ]
  let feature1 = Feature assertion1 badStates (states [[("x", 10)]])
      feature2 = Feature assertion2 Set.empty (states [[("x", 10)], [("x", 20)]])
      feature3 = Feature assertion3 badStates (states [[("x", 20)], [("x", 30)]])
      feature4 = Feature assertion4 badStates (states [[("x", 30)]])
  let clauses = [[feature1], [feature2, feature3], [feature3, feature4]]
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  result <- evalCvi (acceptsAllGoods clauses) env
  assertEqual True result

test_acceptsAllGoods_false = do
  assertion1 <- assertionFromStr "(= x 10)"
  assertion2 <- assertionFromStr "(< x 25)"
  assertion3 <- assertionFromStr "(> x 15)"
  let badStates = states  [ [("x", 0)]
                          , [("x", 1)]
                          ]
  let goodStates = states [ [("x", 10)]
                          , [("x", 20)]
                          , [("x", 30)]
                          ]
  let feature1 = Feature assertion1 badStates (states [[("x", 10)]])
      feature2 = Feature assertion2 Set.empty (states [[("x", 10)], [("x", 20)]])
      feature3 = Feature assertion3 badStates (states [[("x", 20)], [("x", 30)]])
  let clauses = [[feature1], [feature2, feature3]]
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  result <- evalCvi (acceptsAllGoods clauses) env
  assertEqual False result


-- Separator Learning

test_usefulFeatures_rejectsNewAcceptsSame = do
  let
    goodState1 = state [("feat1", 1), ("feat2", 1), ("feat3", 1)]
    goodState2 = state [("feat1", 0), ("feat2", 0), ("feat3", 0)]
    goodState3 = state [("feat1", 1), ("feat2", 0), ("feat3", 0)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
  let
    badState1  = state [("feat1", 0), ("feat2", 0), ("feat3", 1)]
    badState2  = state [("feat1", 1), ("feat2", 1), ("feat3", 0)]
    badStates  = Set.fromList [badState1, badState2]
  feature1 <- feature "(= feat1 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1, goodState3])
  feature2 <- feature "(= feat2 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1])
  feature3 <- feature "(= feat3 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState1])
  let features = [feature1, feature2, feature3]
  let entry = Entry [] [feature1, feature2] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  let task = mapM_ addFeature features >> usefulFeatures entry
  useful <- evalCvi task env
  assertEqual [feature3] useful

test_usefulFeatures_rejectsNewButAcceptsIsDisjoint = do
  let
    goodState1 = state [("feat1", 1), ("feat2", 1), ("feat3", 0)]
    goodState2 = state [("feat1", 0), ("feat2", 0), ("feat3", 1)]
    goodState3 = state [("feat1", 1), ("feat2", 0), ("feat3", 0)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
  let
    badState1  = state [("feat1", 0), ("feat2", 0), ("feat3", 1)]
    badState2  = state [("feat1", 1), ("feat2", 1), ("feat3", 0)]
    badStates  = Set.fromList [badState1, badState2]
  feature1 <- feature "(= feat1 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1, goodState3])
  feature2 <- feature "(= feat2 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1])
  feature3 <- feature "(= feat3 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState2])
  let features = [feature1, feature2, feature3]
  let entry = Entry [] [feature1, feature2] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  let task = mapM_ addFeature features >> usefulFeatures entry
  useful <- evalCvi task env
  assertEqual [] useful

test_usefulFeatures_emptyCandidateWithFeatureAcceptingNewGoods = do
  let
    goodState1 = state [("feat1", 1), ("feat2", 1), ("feat3", 0)]
    goodState2 = state [("feat1", 0), ("feat2", 0), ("feat3", 1)]
    goodState3 = state [("feat1", 1), ("feat2", 0), ("feat3", 0)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
  let
    badState1  = state [("feat1", 0), ("feat2", 1), ("feat3", 1)]
    badState2  = state [("feat1", 1), ("feat2", 0), ("feat3", 0)]
    badStates  = Set.fromList [badState1, badState2]
  feature1 <- feature "(= feat1 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1, goodState3])
  feature2 <- feature "(= feat2 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState1])
  feature3 <- feature "(= feat3 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState2])
  let features = [feature1, feature2, feature3]
  -- feature1 /\ feature2 accept goodState1 while ruling out all bads;
  -- feature1 would kick off a new candidate that accepts goodState3, while
  -- feature3 would kick off a new candidate that accepts goodState2.
  let entry = Entry [[feature1, feature2]] [] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  let task = mapM_ addFeature features >> usefulFeatures entry
  useful <- evalCvi task env
  assertSameElements [feature1, feature3] useful

test_usefulFeatures_candidatesAcceptingSubsetOfClauseFeaturesNotUseful = do
  let
    goodState1 = state [("feat1", 1), ("feat2", 1), ("feat3", 0), ("feat4", 0)]
    goodState2 = state [("feat1", 1), ("feat2", 1), ("feat3", 1), ("feat4", 1)]
    goodState3 = state [("feat1", 0), ("feat2", 0), ("feat3", 1), ("feat4", 0)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
  let
    badState1  = state [("feat1", 0), ("feat2", 1), ("feat3", 0), ("feat4", 0)]
    badState2  = state [("feat1", 1), ("feat2", 0), ("feat3", 1), ("feat4", 1)]
    badStates  = Set.fromList [badState1, badState2]
  feature1 <- feature "(= feat1 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState1, goodState2])
  feature2 <- feature "(= feat2 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState1, goodState2])
  feature3 <- feature "(= feat3 1)"
                      (Set.fromList [badState1])
                      (Set.fromList [goodState2, goodState3])
  feature4 <- feature "(= feat4 1)"
                      (Set.fromList [badState2])
                      (Set.fromList [goodState2])
  let features = [feature1, feature2, feature3, feature4]
  -- feature1 /\ feature2 accept goodState1 and goodState2.
  -- feature3 kicks off a promising clause accepting goodState2 and goodState3
  -- (even though goodState2 is already accepted by feature1 /\ feature2,
  -- goodState3 is not.)
  -- feature4 would normally be a good addition to feature3 as it rejects a new
  -- bad state while accepting a subset of the good states. However, in this
  -- case, the new candidate's (feature3 /\ feature4) set of good states
  -- becomes a subset of the clauses', so there's no need to continue down
  -- this path. (The eventual clause would not add any new good states to
  -- the overall entry.)
  let entry = Entry [[feature1, feature2]] [feature3] False
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  let task = mapM_ addFeature features >> usefulFeatures entry
  useful <- evalCvi task env
  assertEqual [] useful

test_learnSeparator_returnsTrueWhenNoBads =
  let
    badStates = Set.empty
    goodStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  in do
    sep <- evalCvi learnSeparator env
    assertEqual (Just ATrue) sep

test_learnSeparator_returnsFalseWhenNoGoods =
  let
    badStates = Set.fromList [ state[("a", 12), ("b", 4)] ]
    goodStates = Set.empty
    env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  in do
    sep <- evalCvi learnSeparator env
    assertEqual (Just AFalse) sep

test_learnSeparator_returnsTrueWhenNoBadsOrGoods =
  let
    badStates = Set.empty
    goodStates = Set.empty
    env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp []
  in do
    sep <- evalCvi learnSeparator env
    assertEqual (Just ATrue) sep

test_learnSeparator = do
  -- Target separator: (x < 10 || y = 5) && (z < 0)
  expected <- assertionFromStr "(or (and (< x 10) (= y 5)) (< z 0))" :: IO (Assertion Integer)
  -- All the needed feature candidates plus some extras:
  assertions <- sequence $ [ assertionFromStr "(< x 10)"
                           , assertionFromStr "(= y 5)"
                           , assertionFromStr "(< z 0)"
                           , assertionFromStr "(<= x 0)"
                           , assertionFromStr "(= y 2)"
                           , assertionFromStr "(= z -1)"
                           , assertionFromStr "(> x 10)"
                           ] :: IO [Assertion Integer]
  let
    goodState1 = state [("x", 0),  ("y", 5),  ("z",  10)]
    goodState2 = state [("x", 8),  ("y", 5),  ("z",  10)]
    goodState3 = state [("x", 0),  ("y", 2),  ("z", -7)]
    goodState4 = state [("x", 20), ("y", 5),  ("z", -1)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3, goodState4]
  let
    badState1  = state [("x", 20), ("y",  2),  ("z", 8)]
    badState2  = state [("x", 0),  ("y",  0),  ("z", 0)]
    badState3  = state [("x", 12), ("y",  5),  ("z", 9)]
    badState4  = state [("x", -4), ("y", -2),  ("z", 8)]
    badStates  = Set.fromList [badState1, badState2, badState3, badState4]
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp assertions
  let task = do
        features <- mapM assertionToFeature assertions
        mapM_ addFeature features
        mapM_ enqueue =<< mapM featureToEntry features
        learnSeparator
  mActual <- evalCvi task env :: IO (Maybe (Assertion Integer))
  case mActual of
    Nothing     -> assertFailure "Separator learner was unable to find a separator."
    Just actual -> assertEquivalent expected actual


-- Counterexample Updates

test_updateFeature_accepts = do
  feature1 <- feature "(< x 0)" (states [[("x", 1)]]) (states [[("x", -1)]])
  let newBadState = state [("x", -2)]
  let expected = (feature1, Accepts)
  actual <- evalCeili $ updateFeature newBadState feature1
  assertEqual expected actual

test_updateFeature_rejects = do
  feature1 <- feature "(< x 0)" (states [[("x", 1)]]) (states [[("x", -1)]])
  let newBadState = state [("x", 2)]
  expectedFeature <- feature "(< x 0)" (states [[("x", 1)], [("x", 2)]]) (states [[("x", -1)]])
  let expected = (expectedFeature, Rejects)
  actual <- evalCeili $ updateFeature newBadState feature1
  assertEqual expected actual

test_updateClause_allAccept = do
  feature1 <- feature "(< x 0)" (states [[("x", 5)]]) (states [[("x", -1)]])
  feature2 <- feature "(< x 1)" (states [[("x", 5)]]) (states [[("x", -1)]])
  feature3 <- feature "(< x 2)" (states [[("x", 5)]]) (states [[("x", -1)]])
  let clause = [feature1, feature2, feature3]
  let newBadState = state [("x", -2)]
  let expected = (clause, Accepts)
  actual <- evalCeili $ updateClause newBadState clause
  assertEqual expected actual

test_updateClause_someReject = do
  feature1 <- feature "(< x 0)" (states [[("x", 5)]]) (states [[("x", -1)]])
  feature2 <- feature "(< x 1)" (states [[("x", 5)]]) (states [[("x", -1)]])
  feature3 <- feature "(< x 2)" (states [[("x", 5)]]) (states [[("x", -1)]])
  let clause = [feature1, feature2, feature3]
  let newBadState = state [("x", 1)]
  feature1' <- feature "(< x 0)" (states [[("x", 5)], [("x", 1)]]) (states [[("x", -1)]])
  feature2' <- feature "(< x 1)" (states [[("x", 5)], [("x", 1)]]) (states [[("x", -1)]])
  let expected = ([feature1', feature2', feature3], Rejects)
  actual <- evalCeili $ updateClause newBadState clause
  assertEqual expected actual
