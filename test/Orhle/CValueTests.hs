{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.CValueTests(htf_thisModulesTests) where
import Test.Framework
import Orhle.TestUtil

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
    actual <- evalCeili Set.empty task
    assertEqual expected actual

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
    actual <- evalCeili Set.empty task
    assertEqual expected actual

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
    actual <- evalCeili Set.empty task
    assertEqual expected actual

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
    actual <- evalCeili Set.empty task
    assertEqual expected actual


-------------------
-- State Testing --
-------------------

test_testState_concreteTrue = do
  let xVal = Concrete 5
  let yVal = Concrete 6
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(= 11 (+ x y))"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Accepted actual

test_testState_concreteFalse = do
  let xVal = Concrete 5
  let yVal = Concrete 6
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(= 12 (+ x y))"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Rejected actual

test_testState_forallWithinBounds = do
  let xVal = Concrete 5
  let yExpr = Add [Var $ Name "a" 0, Num 1]
  constraint <- assertionFromStr "(and (<= 0 a) (< a 10))"
  let yVal = Constrained yExpr Set.empty (Set.singleton constraint) Set.empty
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(<= (+ x y) 15)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Accepted actual

test_testState_forallOutsideBounds = do
  let xVal = Concrete 5
  let yExpr = Add [Var $ Name "a" 0, Num 1]
  constraint <- assertionFromStr "(and (<= 0 a) (< a 10))"
  let yVal = Constrained yExpr Set.empty (Set.singleton constraint) Set.empty
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(<= (+ x y) 14)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Rejected actual

test_testState_existsWithinBounds = do
  let xVal = Concrete 5
  let yExpr = Add [Var $ Name "c" 0, Num 1]
  constraint <- assertionFromStr "(and (<= 0 c) (< c 10))"
  let yVal = Constrained yExpr (Set.singleton $ Name "c" 0) Set.empty (Set.singleton constraint)
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(<= (+ x y) 10)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Accepted actual

test_testState_existsOutsideBounds = do
  let xVal = Concrete 5
  let yExpr = Add [Var $ Name "c" 0, Num 1]
  constraint <- assertionFromStr "(and (<= 0 c) (< c 10))"
  let yVal = Constrained yExpr (Set.singleton $ Name "c" 0) Set.empty (Set.singleton constraint)
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(> (+ x y) 20)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Rejected actual

test_testState_mixedWithinBounds = do
  let xVal = Concrete 1
  let yExpr = Add [Var $ Name "c" 0, Var $ Name "r" 0]
  aConstraint <- assertionFromStr "(and (<= 0 r) (< r 10))"
  eConstraint <- assertionFromStr "(and (<= 0 c) (< c 10))"
  let yVal = Constrained yExpr
                         (Set.singleton $ Name "c" 0)
                         (Set.singleton aConstraint)
                         (Set.singleton eConstraint)
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  assertion <- assertionFromStr "(= (+ x y) 10)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Accepted actual

test_testState_mixedOutsideBounds = do
  let xVal = Concrete 1
  let yExpr = Add [Var $ Name "c" 0, Var $ Name "r" 0]
  aConstraint <- assertionFromStr "(and (<= 0 r) (< r 10))"
  eConstraint <- assertionFromStr "(and (<= 0 c) (< c 10))"
  let yVal = Constrained yExpr
                         (Set.singleton $ Name "c" 0)
                         (Set.singleton aConstraint)
                         (Set.singleton eConstraint)
  let state = Map.fromList [ (Name "x" 0, xVal)
                           , (Name "y" 0, yVal)
                           ]
  -- No suitable c *for all* r between 0 and 10.
  assertion <- assertionFromStr "(= (+ x y) 11)"
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Rejected actual

test_testState_sums = do
  -- An actual example from a benchmark.
  let originalSum = Constrained
                    (Add [Add [Add [Add [Add [ Num 0
                                             , Var $ Name "original!ret!!3" 0  ]
                                             , Var $ Name "original!ret!!11" 0  ]
                                             , Var $ Name "original!ret!!19" 0 ]
                                             , Var $ Name "original!ret!!27" 0 ]
                                             , Var $ Name "original!ret!!35" 0 ])
                    (Set.fromList [ Name "original!n!3" 0
                                  , Name "original!n!11" 0
                                  , Name "original!n!19" 0
                                  , Name "original!n!27" 0
                                  , Name "original!n!35" 0
                                  , Name "original!ret!!3" 0
                                  , Name "original!ret!!11" 0
                                  , Name "original!ret!!19" 0
                                  , Name "original!ret!!27" 0
                                  , Name "original!ret!!35" 0
                                  ])
                    Set.empty
                    (Set.fromList [ And [ Lte (Num 0) (Var $ Name "original!n!3" 0)
                                        , Lt  (Var $ Name "original!n!3" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!3" 0) (Var $ Name "original!n!3" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!11" 0)
                                        , Lt  (Var $ Name "original!n!11" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!11" 0) (Var $ Name "original!n!11" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!19" 0)
                                        , Lt  (Var $ Name "original!n!19" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!19" 0) (Var $ Name "original!n!19" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!27" 0)
                                        , Lt  (Var $ Name "original!n!27" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!27" 0) (Var $ Name "original!n!27" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!35" 0)
                                        , Lt  (Var $ Name "original!n!35" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!35" 0) (Var $ Name "original!n!35" 0)
                                        ]
                                  ])
  let refinementSum = Constrained
                      (Add [Add [Add [Add [Add [ Num 0
                                               , Var $ Name "refinement!ret!!3" 0  ]
                                               , Var $ Name "refinement!ret!!11" 0  ]
                                               , Var $ Name "refinement!ret!!19" 0 ]
                                               , Var $ Name "refinement!ret!!27" 0 ]
                                               , Var $ Name "refinement!ret!!35" 0 ])
                      Set.empty
                      (Set.fromList [ And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!3" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!11" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!19" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!27" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!35" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    ])
                      Set.empty
  let state = Map.fromList [ (Name "original!sum" 0, originalSum)
                           , (Name "refinement!sum" 0, refinementSum)
                           ]
  let assertion = And [ Lte (Add [ Var $ Name "original!sum" 0
                                 , Mul [ Num (Concrete $ -1)
                                       , Var $ Name "refinement!sum" 0]])
                            (Num $ Concrete 0)
                      , Lte (Add [ Mul [ Num (Concrete $ -1)
                                       , Var $ Name "original!sum" 0]
                                 , Var $ Name "refinement!sum" 0 ])
                            (Num $ Concrete 0)                      ]
  let task = testState @(Assertion CValue) @CValue assertion state
  actual <- evalCeili (namesIn state) task
  assertEqual Accepted actual


------------------
-- Optimization --
------------------

test_optimizeConstraints_sums = do
  -- An actual example from a benchmark.
  let originalSum = Constrained
                    (Add [Add [Add [Add [Add [ Num 0
                                             , Var $ Name "original!ret!!3" 0  ]
                                             , Var $ Name "original!ret!!11" 0  ]
                                             , Var $ Name "original!ret!!19" 0 ]
                                             , Var $ Name "original!ret!!27" 0 ]
                                             , Var $ Name "original!ret!!35" 0 ])
                    (Set.fromList [ Name "original!n!3" 0
                                  , Name "original!n!11" 0
                                  , Name "original!n!19" 0
                                  , Name "original!n!27" 0
                                  , Name "original!n!35" 0
                                  , Name "original!ret!!3" 0
                                  , Name "original!ret!!11" 0
                                  , Name "original!ret!!19" 0
                                  , Name "original!ret!!27" 0
                                  , Name "original!ret!!35" 0
                                  ])
                    Set.empty
                    (Set.fromList [ And [ Lte (Num 0) (Var $ Name "original!n!3" 0)
                                        , Lt  (Var $ Name "original!n!3" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!3" 0) (Var $ Name "original!n!3" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!11" 0)
                                        , Lt  (Var $ Name "original!n!11" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!11" 0) (Var $ Name "original!n!11" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!19" 0)
                                        , Lt  (Var $ Name "original!n!19" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!19" 0) (Var $ Name "original!n!19" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!27" 0)
                                        , Lt  (Var $ Name "original!n!27" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!27" 0) (Var $ Name "original!n!27" 0)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!n!35" 0)
                                        , Lt  (Var $ Name "original!n!35" 0) (Num 10)
                                        , Eq  (Var $ Name "original!ret!!35" 0) (Var $ Name "original!n!35" 0)
                                        ]
                                  ])
  let optimizedOriginalSum = Constrained
                    (Add [Add [Add [Add [Add [ Num 0
                                             , Var $ Name "original!ret!!3" 0  ]
                                             , Var $ Name "original!ret!!11" 0  ]
                                             , Var $ Name "original!ret!!19" 0 ]
                                             , Var $ Name "original!ret!!27" 0 ]
                                             , Var $ Name "original!ret!!35" 0 ])
                    (Set.fromList [ Name "original!n!3" 0
                                  , Name "original!n!11" 0
                                  , Name "original!n!19" 0
                                  , Name "original!n!27" 0
                                  , Name "original!n!35" 0
                                  , Name "original!ret!!3" 0
                                  , Name "original!ret!!11" 0
                                  , Name "original!ret!!19" 0
                                  , Name "original!ret!!27" 0
                                  , Name "original!ret!!35" 0
                                  ])
                    Set.empty
                    (Set.fromList [ And [ Lte (Num 0) (Var $ Name "original!ret!!3" 0)
                                        , Lt  (Var $ Name "original!ret!!3" 0) (Num 10)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!ret!!11" 0)
                                        , Lt  (Var $ Name "original!ret!!11" 0) (Num 10)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!ret!!19" 0)
                                        , Lt  (Var $ Name "original!ret!!19" 0) (Num 10)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!ret!!27" 0)
                                        , Lt  (Var $ Name "original!ret!!27" 0) (Num 10)
                                        ]
                                  , And [ Lte (Num 0) (Var $ Name "original!ret!!35" 0)
                                        , Lt  (Var $ Name "original!ret!!35" 0) (Num 10)
                                        ]
                                  ])
  let refinementSum = Constrained
                      (Add [Add [Add [Add [Add [ Num 0
                                               , Var $ Name "refinement!ret!!3" 0  ]
                                               , Var $ Name "refinement!ret!!11" 0  ]
                                               , Var $ Name "refinement!ret!!19" 0 ]
                                               , Var $ Name "refinement!ret!!27" 0 ]
                                               , Var $ Name "refinement!ret!!35" 0 ])
                      Set.empty
                      (Set.fromList [ And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!3" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!11" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!19" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!27" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!35" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    ])
                      Set.empty

  let optimizedRefinementSum = Constrained
                      (Add [Add [Add [Add [Add [ Num 0
                                               , Var $ Name "refinement!ret!!3" 0  ]
                                               , Var $ Name "refinement!ret!!11" 0  ]
                                               , Var $ Name "refinement!ret!!19" 0 ]
                                               , Var $ Name "refinement!ret!!27" 0 ]
                                               , Var $ Name "refinement!ret!!35" 0 ])
                      Set.empty
                      (Set.fromList [ And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!3" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!11" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!19" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!27" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    , And [ Lte (Num 0) (Var $ Name "refinement!c" 0)
                                          , Lt  (Var $ Name "refinement!c" 0) (Num 5)
                                          , Eq  (Var $ Name "refinement!ret!!35" 0)
                                                (Add [Mul[ Num 2, Var $ Name "refinement!c" 0], Num 1])
                                          ]
                                    ])
                      Set.empty

  let actualOriginalOpt   = optimizeConstraints originalSum
  let actualRefinementOpt = optimizeConstraints refinementSum
  assertEqual optimizedOriginalSum    actualOriginalOpt
  assertEqual optimizedRefinementSum  actualRefinementOpt


-----------------
-- SMT Queries --
-----------------

test_pieFilterClause_concreteConsistent = let
  loopCond  = Lte (Var $ Name "i" 0) (Num $ Concrete 10)
  candidate = Gt (Var $ Name "i" 0) (Num $ Concrete 5)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    actual <- evalCeili (namesIn [loopCond, candidate]) task
    assertEqual True actual

test_pieFilterClause_concreteInconsistent = let
  loopCond  = Lte (Var $ Name "i" 0) (Num $ Concrete 10)
  candidate = Lt (Var $ Name "i" 0) (Num $ Concrete 5)
  task      = pieFilterClause [] [loopCond] ATrue candidate
  in do
    actual <- evalCeili (namesIn [loopCond, candidate]) task
    assertEqual False actual

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
    actual <- evalCeili (namesIn [loopCond, candidate]) task
    assertEqual True actual

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
    actual <- evalCeili (namesIn [loopCond, candidate]) task
    assertEqual False actual

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
    goodResult <- testState @(Assertion CValue) @CValue separator goodState
    badResult  <- testState @(Assertion CValue) @CValue separator badState
    pure $ goodResult == Accepted && badResult == Rejected
  in do
    actual <- evalCeili (namesIn [goodState, badState]) task
    assertEqual True actual
