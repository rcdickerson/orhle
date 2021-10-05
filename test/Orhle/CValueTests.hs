{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CValueTests(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.Name
import Ceili.StatePredicate
import qualified Data.Map as Map
import qualified Data.Set as Set
import Orhle.CValue
import Orhle.SpecImp

c0 = Name "c" 0
c1 = Name "c" 1
c2 = Name "c" 2
x = Name "x" 0
y = Name "y" 0

test_pevalCArith =
  let
    aconstraint = Eq (Var $ Name "foo" 0) (Var $ Name "bar" 0)
    econstraint1 = And [ Lt (Var c0) (Num 10)
                      , Gt (Var c1) (Num 0)
                      , Eq (Var x) (Add [Var c0, Var c1]) ]
    econstraint2 = Eq (Var y) (Var c2)
    arith = Add [ Num $ Concrete 0
                , Num $ Constrained (Add [Var x, Num 5])
                                    (Set.fromList [c0, c1])
                                     Set.empty
                                    (Set.singleton econstraint1)
                , Num $ Constrained (Var y)
                                    (Set.fromList [c2])
                                    (Set.singleton aconstraint)
                                    (Set.singleton econstraint2) ]
    expectedValue = Add [Num 0, Add [Var x, Num 5], Var y]
    expectedCVars = Set.fromList [c0, c1, c2]
    expectedAConstraints = Set.singleton aconstraint
    expectedEConstraints = Set.fromList [econstraint1, econstraint2]
    expected = CValuePEval expectedValue expectedCVars expectedAConstraints expectedEConstraints
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
    retConstr = And [Gte (Num 0) (Var ret), Lt (Var ret) (Num 10)]
    expected = (:[]) $ Map.fromList
        [ (r, Constrained (Var ret) Set.empty (Set.singleton retConstr) Set.empty)
        , (rsum, Constrained (Add [Num 0, (Var ret)]) Set.empty (Set.singleton retConstr) Set.empty) ]
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
        []   -> return $ []
        sts' -> return . concat =<< mapM (\s -> evalSI evalCtxA s prog) sts'
    retConst = And [Gte (Num 0) (Var ret), Lt (Var ret) (Num 10)]
    ret1Const = And [Gte (Num 0) (Var ret1), Lt (Var ret1) (Num 10)]
    expected = (:[]) $ Map.fromList
        [ (r,    Constrained (Var ret1) Set.empty (Set.singleton ret1Const) Set.empty)
        , (rsum, Constrained (Add [Add [Num 0, Var ret], Var ret1])
                              Set.empty
                             (Set.fromList [retConst, ret1Const])
                              Set.empty) ]
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
    expected = (:[]) $ Map.fromList
        [ (r,    Constrained (Var ret)
                             (Set.fromList [c0, ret])
                              Set.empty
                             (Set.singleton $ aAnd [cConst, retConst]))
        , (rsum, Constrained (Add [Num 0, (Var ret)])
                             (Set.fromList [c0, ret])
                              Set.empty
                             (Set.singleton $ aAnd [cConst, retConst])) ]
  in do
    result <- runCeili (defaultEnv $ namesIn prog) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual expected actual

test_twoEEvals =
  let
    evalSI = eval @(SpecImpEvalContext CValue (SpecImpProgram CValue))
    task = do
      evalResult <- evalSI evalCtxE stSum0 prog
      case evalResult of
        []   -> throwError "First evaluation yielded nothing."
        sts' -> return . concat =<< mapM (\s -> evalSI evalCtxE s prog) sts'
    cConst = And [Gte (Num 0) (Var c0), Lt (Var c0) (Num 10)]
    retConst = Eq (Var ret) (Var c0)
    c1Const = And [Gte (Num 0) (Var c1), Lt (Var c1) (Num 10)]
    ret1Const = Eq (Var ret1) (Var c1)
    expected = (:[]) $ Map.fromList
        [ (r,    Constrained (Var ret1)
                             (Set.fromList [c1, ret1])
                              Set.empty
                             (Set.singleton $ aAnd [c1Const, ret1Const]))
        , (rsum, Constrained (Add [Add [Num 0, Var ret], Var ret1])
                             (Set.fromList [c0, c1, ret, ret1])
                              Set.empty
                             (Set.fromList [ aAnd [cConst, retConst]
                                           , aAnd [c1Const, ret1Const]
                                           ])) ]
  in do
    result <- runCeili (defaultEnv $ namesIn prog) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual expected actual


-----------------
-- SMT Queries --
-----------------

test_pieFilterClause_concreteConsistent = let
  loopCond  = Lte (Var $ Name "i" 0) (Num $ Concrete 10)
  candidate = Gt (Var $ Name "i" 0) (Num $ Concrete 5)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    result <- runCeili (defaultEnv $ namesIn [loopCond, candidate]) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual True actual

test_pieFilterClause_concreteInconsistent = let
  loopCond  = Lte (Var $ Name "i" 0) (Num $ Concrete 10)
  candidate = Lt (Var $ Name "i" 0) (Num $ Concrete 5)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    result <- runCeili (defaultEnv $ namesIn [loopCond, candidate]) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual False actual

test_pieFilterClause_abstractConsistent = let
  x_a  = Var $ Name "x_a" 0
  x_e  = Var $ Name "x_e" 0
  cvar = Name "cvar" 0
  iterNum = Constrained (Add [x_a, x_e])
                    (Set.fromList [cvar])
                    (Set.fromList [ Eq (Num 10) x_a ])
                    (Set.fromList [ Lte (Num 0) (Var $ cvar)
                                  , Lt  (Var $ cvar) (Num 10)
                                  , Eq  x_e (Var $ cvar)] )
  loopCond  = Not $ Eq (Var $ Name "i" 0) (Num $ iterNum)
  candidate = Eq (Var $ Name "i" 0) (Num $ Concrete 10)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    result <- runCeili (defaultEnv $ namesIn [loopCond, candidate]) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual True actual

test_pieFilterClause_abstractInconsistent = let
  x_a  = Var $ Name "x_a" 0
  x_e  = Var $ Name "x_e" 0
  cvar = Name "cvar" 0
  iterNum = Constrained (Add [x_a, x_e])
                    (Set.fromList [cvar])
                    (Set.fromList [ Eq (Num 10) x_a ])
                    (Set.fromList [ Lte (Num 0) (Var $ cvar)
                                  , Lt  (Var $ cvar) (Num 10)
                                  , Eq  x_e (Var $ cvar)] )
  loopCond  = Not $ Eq (Var $ Name "i" 0) (Num $ iterNum)
  candidate = Eq (Var $ Name "i" 0) (Num $ Concrete 9)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    result <- runCeili (defaultEnv $ namesIn [loopCond, candidate]) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual False actual

test_separatingQuery = let
  goodState = Map.fromList [ (Name "e!retVal" 0, Concrete 0)
                           , (Name "e!r" 0, Constrained (Var $ Name "e!ret!" 1)
                                                        (Set.fromList [Name "e!n" 1, Name "e!ret!" 1])
                                                         Set.empty
                                                        (Set.singleton $
                                                         And [ Lte (Num 0) (Var $ Name "e!n" 1)
                                                             , Lt (Var $ Name "e!n" 1) (Num 10)
                                                             , Eq (Var $ Name "e!n" 1) (Var $ Name "e!ret!" 1)
                                                             ]))
                           , (Name "e!sum" 0, Constrained (Add [Num 0, Var $ Name "e!ret!" 1])
                                                          (Set.fromList [Name "e!n" 1, Name "e!ret!" 1])
                                                           Set.empty
                                                          (Set.singleton $
                                                            And [ Lte (Num 0) (Var $ Name "e!n" 1)
                                                               , Lt (Var $ Name "e!n" 1) (Num 10)
                                                               , Eq (Var $ Name "e!n" 1) (Var $ Name "e!ret!" 1)
                                                               ]))

                           , (Name "a!retVal" 0, Concrete 0)
                           , (Name "a!r" 0, Constrained (Var $ Name "a!ret!" 1)
                                                        Set.empty
                                                        (Set.singleton $ And [ Lte (Num 0) (Var $ Name "a!ret!" 1)
                                                                             , Lt (Var $ Name "a!ret!" 1) (Num 10)
                                                                             ])
                                                         Set.empty)
                           , (Name "a!sum" 0, Constrained (Add [Num 0, Var $ Name "a!ret!" 1])
                                                           Set.empty
                                                          (Set.singleton $ And [ Lte (Num 0) (Var $ Name "a!ret!" 1)
                                                                               , Lt (Var $ Name "a!ret!" 1) (Num 10)
                                                                               , Eq (Mod (Var $ Name "a!ret!" 1) (Num 2)) (Num 1)
                                                                               ])
                                                           Set.empty)
                           ]
  badState = Map.fromList [ (Name "e!sum" 0, Concrete 12)
                          , (Name "a!sum" 0, Concrete 11) ]
  separator = Eq (Var $ Name "e!sum" 0) (Var $ Name "a!sum" 0)
  task = do
    acceptsGood <- testState @(Assertion CValue) @CValue separator goodState
    acceptsBad  <- testState @(Assertion CValue) @CValue separator badState
    return $ acceptsGood && (not acceptsBad)
  in do
    result <- runCeili (defaultEnv $ namesIn [goodState, badState]) task
    case result of
      Left err -> assertFailure err
      Right actual -> assertEqual True actual
