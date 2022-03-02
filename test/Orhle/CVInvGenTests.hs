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
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

-- Utilities -------------------------------

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

evalCvi :: CviM t a -> CviEnv t -> IO a
evalCvi task env = do
  mResult <- runCeili (defaultEnv Set.empty) $ evalStateT task env
  case mResult of
    Left err     -> assertFailure $ show err
    Right result -> pure result

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
  feature1 <- feature "x < 0" (states [[("x", 4)]]) (states [[("x", -1)]])
  feature2 <- feature "x < 1" (states [[("x", 4)], [("x", 0)]]) (states [[("x", -1)]])
  let
    entry1      = Entry [] [feature1]
    entry2      = Entry [[feature2]] []
    entry1Score = entryScore entry1
    entry2Score = entryScore entry2
    expected    = Map.insert entry1Score (Set.fromList [entry1])
                $ Map.insert entry2Score (Set.fromList [entry2])
                $ (Map.empty :: Queue Integer)
    actual      = qInsert entry1 $ qInsert entry2 $ qInsert entry2 $ (Map.empty :: Queue Integer)
  assertEqual expected actual

test_qPop = do
  feature1 <- feature "x < 0" (states [[("x", 4)]]) (states [[("x", -1)]])
  feature2 <- feature "x < 1" (states [[("x", 4)], [("x", 0)]]) (states [[("x", -1)]])
  let
    entry1      = Entry [] [feature1]
    entry2      = Entry [[feature2]] []
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


-- Learn Separator
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
  expected <- assertionFromStr "(and (or (< x 10) (= y 5)) (< z 0))" :: IO (Assertion Integer)
  -- All the needed feature candidates plus some extras:
  assertions <- sequence $ [ assertionFromStr "(< x 10)"
                           , assertionFromStr "(= y 5)"
                           , assertionFromStr "(< z 0)"
                           , assertionFromStr "(< x 0)"
                           , assertionFromStr "(= y 2)"
                           , assertionFromStr "(= z -1)"
                           , assertionFromStr "(> x 10)"
                           ] :: IO [Assertion Integer]
  let
    goodState1 = state [("x", 0),  ("y", 5),  ("z", -10)]
    goodState2 = state [("x", 0),  ("y", 2),  ("z", -7)]
    goodState3 = state [("x", 20), ("y", 5),  ("z", -1)]
    goodStates = Set.fromList [goodState1, goodState2, goodState3]
  let
    badState1  = state [("x", 20), ("y", 2),  ("z", -8)]
    badState2  = state [("x", 0),  ("y", 0),  ("z",  0)]
    badState3  = state [("x", 12), ("y", 5),  ("z",  9)]
    badState4  = state [("x", -4), ("y", -2), ("z",  8)]
    badStates  = Set.fromList [badState1, badState2, badState3, badState4]
  let env = mkCviEnv (Job badStates goodStates ATrue impSkip ATrue) dummyWp assertions
  mActual <- evalCvi learnSeparator env :: IO (Maybe (Assertion Integer))
  case mActual of
    Nothing     -> assertFailure "Separator learner was unable to find a separator."
    Just actual -> assertEquivalent expected actual
