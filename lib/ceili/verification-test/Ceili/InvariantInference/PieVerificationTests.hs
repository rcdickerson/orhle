{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.InvariantInference.PieVerificationTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.FeatureLearning.LinearInequalities
import Ceili.FeatureLearning.Pie
import Ceili.InvariantInference.LoopInvGen
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import Ceili.SMTString
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Log.FastLogger

data EmptyPieContextProvider = EmptyPieContextProvider
instance ImpPieContextProvider EmptyPieContextProvider Integer where
  impPieCtx _ = ImpPieContext Map.empty Set.empty Set.empty

env :: ImpProgram t -> Assertion t -> Env
env prog post = defaultEnv names
  where
    names = Set.union (namesIn prog) (namesIn post)

assertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                 => Assertion t -> Assertion t -> IO ()
assertEquivalent a1 a2 = do
  let iff = And [ Imp a1 a2, Imp a2 a1 ]
  result <- withFastLogger LogNone $ \logger ->
            SMT.checkValidFL logger iff
  case result of
    SMT.Valid        -> return () -- pass
    SMT.Invalid s    -> assertFailure s
    SMT.ValidUnknown -> assertFailure "Unable to establish equivalence."

runAndAssertEquivalent :: (SMTString t, SMTTypeString t, ValidCheckable t)
                       => Env -> Assertion t -> Ceili (Maybe (Assertion t)) -> IO ()
runAndAssertEquivalent env expected actual = do
  result <- runCeili env actual
  case result of
    Left err         -> assertFailure err
    Right mAssertion ->
      case mAssertion of
        Nothing     -> assertFailure "Expected assertion, got Nothing."
        Just actual -> assertEquivalent expected actual

-- This is the "Slow Subtraction" example from Software Foundations, Pierce et al.
-- https://softwarefoundations.cis.upenn.edu/plf-current/Hoare2.html
test_loopInvGen = let
  x = Name "x" 0
  y = Name "y" 0
  n = Name "n" 0
  m = Name "m" 0
  cond = BNe (AVar x) (ALit @Integer 0)
  body = impSeq [ impAsgn y $ ASub (AVar y) (ALit @Integer 1)
                , impAsgn x $ ASub (AVar x) (ALit @Integer 1)]
  post = (Eq (Var y) (Sub [Var n, Var m]))
  names = Set.union (namesIn body) (namesIn post)
  lits = litsIn body
  -- Loop will always start in a state where x = m and y = n.
  tests = [ Map.fromList [(x, 0), (y, 0), (m, 0), (n, 0)]
          , Map.fromList [(x, 5), (y, 3), (m, 5), (n, 3)]
          , Map.fromList [(x, 3), (y, 5), (m, 3), (n, 5)]
          ]
  expected = Eq (Sub [Var y, Var x])
                (Sub [Var n, Var m])
  in runAndAssertEquivalent (env body post) expected
     $ loopInvGen EmptyPieContextProvider impBackwardPT [bexpToAssertion cond] body post tests
     $ pie Set.empty (linearInequalities lits)
