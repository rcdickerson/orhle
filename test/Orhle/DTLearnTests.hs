{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.DTLearnTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities ( linearInequalities )
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.DTLearn
import System.Log.FastLogger

assertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                 => Assertion t -> Assertion t -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure $ unlines ["Not equivalent: ", showSMT a1, "and", showSMT a2, "model:", s]
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence, solver returned UNK."

runAndAssertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                       => Assertion t -> Ceili (Maybe (Assertion t)) -> IO ()
runAndAssertEquivalent expected actual = do
  result <- runCeili emptyEnv actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing        -> assertFailure "Expected assertion, got Nothing."
        Just assertion -> assertEquivalent expected assertion

-- test_simpleSeparator = let
--   x          = Name "x" 0
--   names      = Set.singleton x
--   lits       = Set.empty
--   badStates  = [ Map.fromList [(Name "x" 0,  0)]
--                , Map.fromList [(Name "x" 0, -1)]
--                , Map.fromList [(Name "x" 0, -5)] ]
--   goodStates = [ Map.fromList [(Name "x" 0, 1)]
--                , Map.fromList [(Name "x" 0, 5)] ]
--   expected   = Lt @Integer (Num 0) (Var x)
--   in runAndAssertEquivalent expected $ learnSeparator 2 (linearInequalities names lits) badStates goodStates
