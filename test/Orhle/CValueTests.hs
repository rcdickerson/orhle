{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CValueTests(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.Name
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.CValue
import Orhle.SpecImp

c0 = Name "c0" 0
c1 = Name "c1" 0
c2 = Name "c2" 0
x = Name "x" 0
y = Name "y" 0

test_pevalCArith =
  let
    constraint1 = And [ Lt (Var c0) (Num 10)
                      , Gt (Var c1) (Num 0)
                      , Eq (Var x) (Add [Var c0, Var c1]) ]
    constraint2 = Eq (Var y) (Var c2)
    arith = Add [ Num $ Concrete 0
                , Num $ WithChoice (Set.fromList [c0, c1])
                                   (Set.singleton constraint1)
                                   (Add [Var x, Num 5])
                , Num $ WithChoice (Set.fromList [c2])
                                   (Set.singleton constraint2)
                                   (Var y)]
    expectedCVars = Set.fromList [c0, c1, c2]
    expectedConstraints = Set.fromList [constraint1, constraint2]
    expectedValue = Add [Num 0, Add [Var x, Num 5], Var y]
    expected = CValuePEval expectedCVars expectedConstraints expectedValue
    actual = pevalCArith arith
  in assertEqual expected actual


------------------------------
-- Specification Evaluation --
------------------------------

rsum = Name "rsum" 0
r = Name "r" 0
ret = Name "ret!" 0
ret1 = Name "ret!" 1

randSpecA = Specification @CValue [] [ret] []
              ATrue
              (And [ Gte (Num $ Concrete 0) (Var ret)
                   , Lt  (Var ret) (Num $ Concrete 10)])
randSpecE = Specification @CValue [] [ret] [c0]
              (And [ Gte (Num $ Concrete 0) (Var c0)
                   , Lt (Var c0) (Num $ Concrete 10)])
              (Eq (Var ret) (Var c0))

specEnvA = FunSpecEnv { fse_aspecs = Map.fromList [("rand", randSpecA)]
                      , fse_especs = Map.empty }
specImpEnvA = SpecImpEnv Map.empty specEnvA
evalCtxA = SpecImpEvalContext (Fuel 100) specImpEnvA

specEnvE = FunSpecEnv { fse_aspecs = Map.empty
                      , fse_especs = Map.fromList [("rand", randSpecE)] }
specImpEnvE = SpecImpEnv Map.empty specEnvE
evalCtxE = SpecImpEvalContext (Fuel 100) specImpEnvE

stSum0 = Map.fromList [(rsum, Concrete 0)]

prog = impSeq [ specCall "rand" [] [r]
              , impAsgn rsum $ AAdd (AVar rsum) (AVar r)
              ] :: SpecImpProgram CValue

test_oneAEval =
  let
    evalSI = eval @(SpecImpEvalContext CValue (SpecImpProgram CValue))
    task = evalSI evalCtxA stSum0 prog
    retConst = And [Gte (Num 0) (Var ret), Lt (Var ret) (Num 10)]
    withChoice = WithChoice Set.empty (Set.fromList [ATrue, retConst])
    expected = Just $ Map.fromList
        [ (r, withChoice $ Var ret)
        , (rsum, withChoice $ Add [Num 0, (Var ret)]) ]
  in do
    result <- runCeili (defaultEnv $ namesIn prog) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual expected actual

test_twoAEvals =
  let
    evalSI = eval @(SpecImpEvalContext CValue (SpecImpProgram CValue))
    task = do
      evalResult <- evalSI evalCtxA stSum0 prog
      case evalResult of
        Nothing  -> return $ Nothing
        Just st' -> evalSI evalCtxA st' prog
    retConst = And [Gte (Num 0) (Var ret), Lt (Var ret) (Num 10)]
    ret1Const = And [Gte (Num 0) (Var ret1), Lt (Var ret1) (Num 10)]
    expected = Just $ Map.fromList
        [ (r,   WithChoice Set.empty
                           (Set.fromList [ATrue, ret1Const])
                           (Var ret1))
        , (rsum, WithChoice Set.empty
                            (Set.fromList [ATrue, retConst, ret1Const])
                            (Add [Add [Num 0, Var ret], Var ret1])) ]
  in do
    result <- runCeili (defaultEnv $ namesIn prog) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual expected actual

test_oneEEval =
  let
    evalSI = eval @(SpecImpEvalContext CValue (SpecImpProgram CValue))
    task = evalSI evalCtxE stSum0 prog
    cConst = And [Gte (Num 0) (Var c0), Lt (Var c0) (Num 10)]
    retConst = Eq (Var ret) (Var c0)
    expected = Just $ Map.fromList
        [ (r,    WithChoice (Set.singleton c0)
                            (Set.fromList [cConst, retConst])
                            (Var ret))
        , (rsum, WithChoice (Set.singleton c0)
                            (Set.fromList [cConst, retConst])
                            (Add [Num 0, (Var ret)])) ]
  in do
    result <- runCeili (defaultEnv $ namesIn prog) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual expected actual
