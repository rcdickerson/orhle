{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.ImpVerificationTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion ( Arith(..), Assertion(..) )
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Ceili.Language.ImpParser
import Ceili.Literal
import Ceili.Name
import qualified Ceili.SMT as SMT
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.FilePath

data ExpectResult = ExpectSuccess | ExpectFailure

envFromProg :: ImpProgram t -> Env
envFromProg prog = defaultEnv (namesIn prog)

assertSMTResult expected result =
  case (expected, result) of
    (ExpectSuccess, SMT.Valid) -> return ()
    (ExpectFailure, SMT.Invalid _) -> return ()
    (ExpectSuccess, SMT.Invalid msg) -> assertFailure
      $ "Expected VALID but was INVALID. Message: " ++ msg
    (ExpectFailure, SMT.Valid) -> assertFailure
      $ "Expected INVALID but was VALID"
    _ -> assertFailure "Unknown SMT result"

assertRunsWithoutErrors env task check = do
  spOrErr <- runCeili env task
  case spOrErr of
    Left err     -> assertFailure $ show err
    Right result -> check result

assertRunsWithError env task expectedErr = do
  spOrErr <- runCeili env task
  case spOrErr of
    Left err     -> assertEqual expectedErr err
    Right result -> assertFailure $ "Unexpected success: " ++ show result

readImpFile fileName = do
  readFile $ "verification-test"
         </> "resources"
         </> "imp"
         </> fileName

readAndParse :: String -> IO (ImpProgram Integer)
readAndParse path = do
  progStr <- readImpFile path
  case parseImp progStr of
    Left  err     -> assertFailure $ "Parse error: " ++ (show err)
    Right program -> populateLoopIds @(ImpProgram Integer) @Integer program

mkTestStartStates :: CollectableNames n => n -> [ProgState Integer]
mkTestStartStates cnames =
  let names = Set.toList $ namesIn cnames
  in [ Map.fromList $ map (\n -> (n, 0)) names
     , Map.fromList $ map (\n -> (n, 1)) names
     , Map.fromList $ map (\n -> (n, -1)) names
     ]

runForward :: ExpectResult -> String -> Assertion Integer -> Assertion Integer -> IO ()
runForward expectedResult progFile pre post = do
  prog <- readAndParse progFile
  assertRunsWithoutErrors (envFromProg prog) (impForwardPT () prog pre) $
    \result -> do
      smtResult <- SMT.checkValidNoLog $ Imp result post
      assertSMTResult expectedResult smtResult

runBackward :: ExpectResult -> String -> Assertion Integer -> Assertion Integer -> IO ()
runBackward expectedResult progFile pre post = do
  prog <- readAndParse progFile
  let findWP = do
        loopHeadStates <- collectLoopHeadStates (Fuel 1000) (mkTestStartStates prog) prog
        let ctx = ImpPieContext loopHeadStates (namesIn prog) (litsIn prog)
        impBackwardPT ctx prog post
  assertRunsWithoutErrors (envFromProg prog) findWP $
    \result -> do
      smtResult <- SMT.checkValidNoLog $ Imp pre result
      assertSMTResult expectedResult smtResult


varX = Var $ Name "x" 0
varY = Var $ Name "y" 0


test_forward_inferInv1_valid    = runForward  ExpectSuccess "inferInv1.imp" ATrue $ Eq varX varY
test_forward_inferInv1_invalid  = runForward  ExpectFailure "inferInv1.imp" ATrue $ Not (Eq varX varY)
test_backward_inferInv1_valid   = runBackward ExpectSuccess "inferInv1.imp" ATrue $ Eq varX varY
test_backward_inferInv1_invalid = runBackward ExpectFailure "inferInv1.imp" ATrue $ Not (Eq varX varY)
