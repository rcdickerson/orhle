{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.DTInvGenTests(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Control.Monad.Trans.State ( evalStateT, get )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Map ( Map )
import qualified Data.Map as Map
import Orhle.DTInvGen

runDti :: DtiM t r -> DtiEnv t -> IO r
runDti task env =
  let
    ceiliEnv = defaultEnv Set.empty
  in do
    mResult <- runCeili ceiliEnv $ evalStateT task env
    case mResult of
      Left msg -> assertFailure msg
      Right result -> pure result

testDtiEnv badStates goodStates queue features candidates names =
  let wpTransform _ = pure $ ATrue
  in DtiEnv badStates goodStates [] queue features candidates 12 names wpTransform

assertionFromStr :: AssertionParseable t => String -> IO (Assertion t)
assertionFromStr str =
  let assertion = parseAssertion str
  in case assertion of
    Left err -> assertFailure (show err)
    Right a  -> pure a


test_updateQueue_emptyQueue = do
  let queue = Map.empty :: DTLQueue Integer
  let env = testDtiEnv Set.empty Set.empty Map.empty Set.empty [] []
  queue' <- runDti (updateQueue Set.empty Set.empty queue) env
  assertEqual queue queue'

test_updateQueue_updatesBadsAndRemovesEntryWithBadClause = do
  assertion1 <- assertionFromStr "(< x 0)" :: IO (Assertion Integer)
  assertion2 <- assertionFromStr "(< x 1)" :: IO (Assertion Integer)
  let
    -- To start, a single bad state and two clauses that reject it.
    goodState1 = Map.fromList [(Name "x" 0, 20)]
    goodState2 = Map.fromList [(Name "x" 0, -20)]
    badState   = Map.fromList [(Name "x" 0, -10)]
    feature1   = Feature assertion1 (Set.singleton badState) (Set.singleton goodState2)
    feature2   = Feature assertion2 (Set.singleton badState) (Set.singleton goodState2)
    clause1    = Clause [feature1]
                        (Set.singleton badState)
                        (Set.singleton goodState1)
    clause2    = Clause [feature2]
                        (Set.singleton badState)
                        (Set.singleton goodState1)
    entry1     = DTLQueueEntry [clause1] emptyCandidate (Set.singleton goodState2)
    entry2     = DTLQueueEntry [clause2] emptyCandidate (Set.singleton goodState2)
    queue      = qInsert entry1 $ qInsert entry2 $ Map.empty
    -- Add a new bad state such that clause2 no longer rejects all bads.
    addedBadState = Map.fromList [(Name "x" 0, 0)]
    newBadStates  = Set.fromList [badState, addedBadState]
    newClause1    = Clause [Feature assertion1 newBadStates (Set.singleton goodState2)]
                    newBadStates
                    (Set.singleton goodState1)
    newEntry1     = DTLQueueEntry [newClause1] emptyCandidate (Set.singleton goodState2)
    -- The second clause should be evicted from the queue.
    expected      = qInsert newEntry1 Map.empty
  let env = testDtiEnv newBadStates
                       (Set.fromList [goodState1, goodState2])
                       queue
                       (Set.fromList [feature1, feature2])
                       []
                       [Name "x" 0]
  queue' <- runDti (updateQueue (Set.singleton badState) (Set.singleton addedBadState) queue) env
  assertEqual expected queue'

test_addBadState = do
  assertion1 <- assertionFromStr "(= x 5)"  :: IO (Assertion Integer)
  assertion2 <- assertionFromStr "(= x 10)" :: IO (Assertion Integer)
  assertion3 <- assertionFromStr "(< y 30)" :: IO (Assertion Integer)
  assertion4 <- assertionFromStr "(< y 40)" :: IO (Assertion Integer)
  let
    names      = [Name "x" 0, Name "y" 0]
    loopConds  = [ATrue]
    -- Good States
    goodState1 = Map.fromList [(Name "x" 0, 5),  (Name "y" 0, 15)]
    goodState2 = Map.fromList [(Name "x" 0, 10), (Name "y" 0, 30)]
    goodState3 = Map.fromList [(Name "x" 0, 12), (Name "y" 0, 36)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
    -- Bad States
    badState1  = Map.fromList [(Name "x" 0, 5),  (Name "y" 0, 12)]
    badState2  = Map.fromList [(Name "x" 0, 7),  (Name "y" 0, 7)]
    badStates  = Set.fromList [badState1, badState2]


      -- Before update.
    feature1   = Feature assertion1
                         (Set.singleton badState2)
                         (Set.singleton goodState1)
    feature2   = Feature assertion2
                         (Set.fromList [badState1, badState2])
                         (Set.singleton goodState2)
    features   = [feature1, feature2]
    candidates = [assertion3, assertion4]
    clause2    = Clause [feature2]
                        (Set.fromList [badState1, badState2])
                        (Set.singleton goodState2)
    entry1     = DTLQueueEntry []
                               (ClauseCandidate [feature1]
                                                (Set.fromList [badState2])
                                                (Set.fromList [goodState1]))
                               (Set.fromList [goodState2, goodState3])
    entry2     = DTLQueueEntry [clause2]
                               emptyCandidate
                               (Set.fromList [])
    queue      = qInsert entry1 $ qInsert entry2 $ Map.empty
    oldEnv     = DtiEnv goodStates
                        badStates
                        loopConds
                        queue
                        (Set.fromList features)
                        candidates
                        4
                        names
                        (\_ -> pure ATrue)
  -- After update.
  let
    newBadState = Map.fromList [(Name "x" 0, 10), (Name "y" 0, 30)]
    -- Feature 1 rejects the new bad state.
    feature1' = Feature assertion1
                        (Set.fromList [newBadState, badState2])
                        (Set.singleton goodState1)
    entry1'  = DTLQueueEntry []
                             (ClauseCandidate [feature1']
                                              (Set.fromList [newBadState, badState2])
                                              (Set.fromList [goodState1]))
                             (Set.fromList [goodState2, goodState3])

    -- Entry2 no longer rejects all bads, removed from queue.

    -- A newly useful assertion has entered the game.
    feature3 = Feature assertion3
                       (Set.singleton newBadState)
                       (Set.fromList [goodState1])
    entry3'  = DTLQueueEntry []
                             (ClauseCandidate [feature3]
                                              (Set.fromList [newBadState])
                                              (Set.fromList [goodState1]))
                             (Set.fromList [goodState2, goodState3])
    expectedGoodStates = goodStates
    expectedBadStates  = Set.insert newBadState badStates
    expectedQueue      = qInsert entry1' $ qInsert entry3' $ Map.empty
    expectedFeatures   = Set.fromList [feature1, feature2, feature3]
    expectedCandidates = [assertion4]
  -- Verify.
  let task = addBadState newBadState >> get
  mResult <- runCeili (defaultEnv $ Set.fromList names) $ evalStateT task oldEnv
  case mResult of
    Left err -> assertFailure err
    Right (DtiEnv goodStates' badStates' _ queue' features' candidates' _ _ _) -> do
      assertEqual expectedGoodStates goodStates'
      assertEqual expectedBadStates  badStates'
      assertEqual expectedQueue      queue'
      assertEqual expectedFeatures   features'
      assertEqual expectedCandidates candidates'
