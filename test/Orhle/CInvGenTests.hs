{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CInvGenTests(htf_thisModulesTests) where
import Test.Framework
import Orhle.TestUtil

import Orhle.CInvGen

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Control.Monad.Trans.State ( evalStateT, runStateT )
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

runCI :: CiM t a -> CIEnv t -> IO (CIEnv t)
runCI task env = do
  (a, env) <- evalCeili $ runStateT task env
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
  let clause1 = RootClause (clause [feature1, feature2]) []
  let clause2 = RootClause (clause [feature3]) []
  let expected = Set.fromList [state3]
  let env = CIEnv Map.empty Set.empty states [clause1, clause2] Set.empty [] (\ _ -> pure ATrue) [] 8
  actual <- evalCI getRemainingGoods env
  assertEqual expected actual

test_buildCurrentResult = do
  feature1 <- feature "(< x 4)" Set.empty Set.empty
  feature2 <- feature "(< x 3)" Set.empty Set.empty
  feature3 <- feature "(< x 2)" Set.empty Set.empty
  let clause1 = RootClause (clause [feature1]) []
  let clause2 = RootClause (clause [feature2, feature3]) []
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
  -- To start, our root clauses cover good states 1 and 2...
  feature1 <- feature "(and (= x 1) (< y 0))" badStates (Set.fromList [goodState1])
  feature2 <- feature "(and (= x 2) (< y 0))" badStates (Set.fromList [goodState2])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
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


-- RootClause Clause Update

test_addRootClause_noCover = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature "(= x 1)" Set.empty (Set.fromList [goodState1])
  feature2 <- feature "(= x 2)" Set.empty (Set.fromList [goodState2])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers good state 3.
  newFeature <- feature "(= x 3)" Set.empty (Set.fromList [goodState3])
  let newClause = Clause [newFeature] (Set.fromList [goodState3])
  -- Our new clause list should include all three root clauses (the two original plus one new).
  let expected = [root1, root2, RootClause newClause []]
  let env = CIEnv Map.empty Set.empty goodStates [root1, root2] Set.empty [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_singleCover = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature "(= x 1)" Set.empty (Set.fromList [goodState1])
  feature2 <- feature "(= x 2)" Set.empty (Set.fromList [goodState2])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers good states 2 and 3.
  newFeature <- feature "(> x 1)" Set.empty (Set.fromList [goodState2, goodState3])
  let newClause = Clause [newFeature] (Set.fromList [goodState2, goodState3])
  -- Our new clause list should include the first root, plus the new clause covering
  -- the second original root.
  let expected = [root1, RootClause newClause [root2]]
  let env = CIEnv Map.empty Set.empty goodStates [root1, root2] Set.empty [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_multiCover = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature "(= x 1)" Set.empty (Set.fromList [goodState1])
  feature2 <- feature "(= x 2)" Set.empty (Set.fromList [goodState2])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that covers all good states.
  newFeature <- feature "(< x 4)" Set.empty goodStates
  let newClause = Clause [newFeature] goodStates
  -- Our new clause list should include only the new clause, covering both original roots.
  let expected = [RootClause newClause [root1, root2]]
  let env = CIEnv Map.empty Set.empty goodStates [root1, root2] Set.empty [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_exactCover = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3]
  -- To start, our root clauses cover good states 1 and 2.
  feature1 <- feature "(= x 1)" Set.empty (Set.fromList [goodState1])
  feature2 <- feature "(= x 2)" Set.empty (Set.fromList [goodState2])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
  let clause2 = Clause [feature2] (Set.fromList [goodState2])
  let root1 = RootClause clause1 []
  let root2 = RootClause clause2 []
  -- Add a clause that also covers good states 1 and 2.
  newFeature <- feature "(or (= x 1) (= x 2))" Set.empty (Set.fromList [goodState1, goodState2])
  let newClause = Clause [newFeature] (Set.fromList [goodState1, goodState2])
  -- The root clause list should now be the new clause covering the two previous clauses.
  let expected = [RootClause newClause [root1, root2]]
  let env = CIEnv Map.empty Set.empty goodStates [root1, root2] Set.empty [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)

test_addRootClause_deepInsert = do
  let goodState1 = state [("x", 1)]
      goodState2 = state [("x", 2)]
      goodState3 = state [("x", 3)]
      goodState4 = state [("x", 4)]
      goodState5 = state [("x", 5)]
      goodStates = Set.fromList [goodState1, goodState2, goodState3, goodState4, goodState5]
  -- To start, our root clauses form a linear chain of inclusions:
  --   root4 <--- root3 <--- root2 <--- root1
  feature1 <- feature "(<= x 5)" Set.empty (Set.fromList [goodState5])
  feature2 <- feature "(<= x 3)" Set.empty (Set.fromList [goodState3, goodState4, goodState5])
  feature3 <- feature "(<= x 2)" Set.empty (Set.fromList [goodState2, goodState3, goodState4, goodState5])
  feature4 <- feature "(<= x 1)" Set.empty (Set.fromList [goodState1, goodState2, goodState3, goodState4, goodState5])
  let clause1 = Clause [feature1] (Set.fromList [goodState5])
      clause2 = Clause [feature2] (Set.fromList [goodState3, goodState4, goodState5])
      clause3 = Clause [feature3] (Set.fromList [goodState2, goodState3, goodState4, goodState5])
      clause4 = Clause [feature4] (Set.fromList [goodState1, goodState2, goodState3, goodState4, goodState5])
  let root1 = RootClause clause1 []
      root2 = RootClause clause2 [root1]
      root3 = RootClause clause3 [root2]
      root4 = RootClause clause4 [root3]
      roots = [root4]
  -- Add a clause that needs to be inserted between root2 and root1
  --   root4 <--- root3 <--- root2 <--- *newClause* <--- root1
  newFeature <- feature "(<= x 4)" Set.empty (Set.fromList [goodState4, goodState5])
  let newClause = Clause [newFeature] (Set.fromList [goodState4, goodState5])
  let root1'  = RootClause clause1 []
      newRoot = RootClause newClause [root1']
      root2'  = RootClause clause2 [newRoot]
      root3'  = RootClause clause3 [root2']
      root4'  = RootClause clause4 [root3']
      expected = [root4']
  let env = CIEnv Map.empty Set.empty goodStates roots Set.empty [] (\_ -> pure ATrue) [] 8
  actual <- evalCI (addRootClause newClause >> getRootClauses) env
  assertEqual (Set.fromList expected) (Set.fromList actual)


-- Counterexample Update

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

test_updateQueue = do
  let states0   = states [[("x", 0)]]
      states013 = states [[("x", 0)], [("x", 1)], [("x", 3)]]
  let goods = states [[("x", 10)]]
  feature1 <- feature "(> x 1)" states0   goods
  feature2 <- feature "(> x 3)" states013 goods
  feature3 <- feature "(> x 4)" states013 goods
  let queue = qInsert (Entry [feature1]           states0   goods)
            $ qInsert (Entry [feature2]           states013 goods)
            $ qInsert (Entry [feature3]           states013 goods)
            $ qInsert (Entry [feature1, feature2] states013 goods)
            $ Map.empty
  let newBadState = state [("x", 2)]
  let states0123 = states [[("x", 0)], [("x", 1)], [("x", 2)], [("x", 3)]]
  feature2' <- feature "(> x 3)" states0123 goods
  feature3' <- feature "(> x 4)" states0123 goods
  let expected = qInsert (Entry [feature1]            states0    goods)
               $ qInsert (Entry [feature2']           states0123 goods)
               $ qInsert (Entry [feature3']           states0123 goods)
               $ qInsert (Entry [feature1, feature2'] states0123 goods)
               $ Map.empty
  actual <- evalCeili $ updateQueue newBadState queue
  assertEqual expected actual

test_addNewlyUsefulCandidates = do
  assertion1 <- assertionFromStr "(< x 1)" -- Rejects all goods, eliminated when we look
                                           -- at it for rejecting some bad state (but not
                                           -- sooner).
  assertion2 <- assertionFromStr "(< x 2)" -- Rejects new bad while accepting goods.
  assertion3 <- assertionFromStr "(< x 3)" -- Does not reject new bad.
  assertion4 <- assertionFromStr "(< x 4)" -- Does not reject new bad.
  let candidates = [assertion1, assertion2, assertion3, assertion4]
  let goodStates = states [[("x", 1)]]
  let newBadState = state [("x", 2)]
  let newBadStates = Set.singleton newBadState
  expectedFeature2 <- feature "(< x 2)" (states [[("x", 2)]]) (states [[("x", 1)]])
  let expectedQueue = qInsert (Entry [expectedFeature2] (states [[("x", 2)]]) (states [[("x", 1)]]))
                    $ Map.empty
  let expectedCandidates' = [assertion3, assertion4]
  let expectedFeatures' = Set.fromList [expectedFeature2]
  let env = CIEnv Map.empty newBadStates goodStates [] Set.empty candidates (\_ -> pure ATrue) [] 8
  let task = do
        addNewlyUsefulCandidates newBadState
        queue <- getQueue
        fCandidates <- getFeatureCandidates
        features <- getFeatures
        pure (queue, fCandidates, features)
  (actualQueue, actualCandidates', actualFeatures') <- evalCI task env
  assertEqual expectedQueue       actualQueue
  assertEqual expectedCandidates' actualCandidates'
  assertEqual expectedFeatures'   actualFeatures'

test_updateRootClauses = do
  -- Dummy good states: assertions don't actually have to accept them
  -- to make the test setup work.
  let goodState1 = state [("a", 1)]
      goodState2 = state [("a", 2)]
      goodState3 = state [("a", 3)]
      goodState4 = state [("a", 4)]
      goodState5 = state [("a", 5)]
  let badState1     = state [("x", 1), ("y", 1), ("z", 1)]
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
  feature1 <- feature assertion1 origBadStates (Set.fromList [ goodState1 ])
  feature2 <- feature assertion2 origBadStates (Set.fromList [ goodState2 ])
  feature3 <- feature assertion3 origBadStates (Set.fromList [ goodState3 ])
  feature4 <- feature assertion4 origBadStates (Set.fromList [ goodState2
                                                             , goodState4 ])
  feature5 <- feature assertion5 origBadStates (Set.fromList [ goodState3
                                                             , goodState5 ])
  feature6 <- feature assertion6 origBadStates (Set.fromList [ goodState2
                                                             , goodState3
                                                             , goodState4
                                                             , goodState5 ])
  let clause1 = Clause [feature1] (Set.fromList [goodState1])
      clause2 = Clause [feature2] (Set.fromList [goodState2])
      clause3 = Clause [feature3] (Set.fromList [goodState3])
      clause4 = Clause [feature4] (Set.fromList [goodState2, goodState4])
      clause5 = Clause [feature5] (Set.fromList [goodState3, goodState5])
      clause6 = Clause [feature6] (Set.fromList [goodState2, goodState3, goodState4, goodState5])
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
  let newBadState  = state [("x", 1), ("y", -1), ("z", 1)]
      newBadStates = Set.insert newBadState origBadStates
  feature1' <- feature assertion1 newBadStates  (Set.fromList [ goodState1 ])
  feature2' <- feature assertion2 newBadStates  (Set.fromList [ goodState2 ])
  feature3' <- feature assertion3 newBadStates  (Set.fromList [ goodState3 ])
  feature5' <- feature assertion5 newBadStates  (Set.fromList [ goodState3
                                                              , goodState5 ])
  let clause1' = Clause [feature1'] (Set.fromList [goodState1])
      clause2' = Clause [feature2'] (Set.fromList [goodState2])
      clause3' = Clause [feature3'] (Set.fromList [goodState3])
      clause5' = Clause [feature5'] (Set.fromList [goodState3, goodState5])
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
  let root1' = RootClause clause1' []
      root2' = RootClause clause2' []
      root3' = RootClause clause3' []
      root5' = RootClause clause5' [root3']
      expected = [root1', root2', root5']
  actual <- evalCeili (updateRootClauses newBadState origRootList)
  assertEqual expected actual

test_updateRootClauses_combinesCoverage = do
  -- Dummy good states: assertions don't actually have to accept them
  -- to make the test setup work.
  let goodState1    = state [("a", 1)]
      goodState2    = state [("a", 2)]
  let badState1     = state [("x", 10)]
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
  feature1 <- feature "(< x 5)" origBadStates (Set.fromList [goodState1, goodState2])
  feature2 <- feature "(< x 4)" origBadStates (Set.fromList [goodState1, goodState2])
  feature3 <- feature "(= x 3)" origBadStates (Set.fromList [goodState1])
  let clause1 = Clause [feature1] (Set.fromList [goodState1, goodState2])
      clause2 = Clause [feature2] (Set.fromList [goodState1, goodState2])
      clause3 = Clause [feature3] (Set.fromList [goodState1])
  let root2 = RootClause clause2 []
      root3 = RootClause clause3 []
      root1 = RootClause clause1 [root2, root3]
      origRootList = [root1]
  --
  -- A counterexample which kills root1.
  --
  let newBadState  = state [("x", 4)]
      newBadStates = Set.insert newBadState origBadStates
  feature2' <- feature "(< x 4)" newBadStates (Set.fromList [goodState1, goodState2])
  feature3' <- feature "(= x 3)" newBadStates (Set.fromList [goodState1])
  let clause2' = Clause [feature2'] (Set.fromList [goodState1, goodState2])
      clause3' = Clause [feature3'] (Set.fromList [goodState1])
  --
  -- After update, the root list should be [root2] with root2 now covering root3:
  --
  --    root2 <---- root3
  --
  let root3' = RootClause clause3' []
      root2' = RootClause clause2' [root3']
      expected = [root2']
  actual <- evalCeili (updateRootClauses newBadState origRootList)
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
  mActual  <- evalCeili $ cInvGen cfg job
  case mActual of
    Nothing     -> assertFailure "Unable to find separator."
    Just actual -> assertEquivalent expected actual
