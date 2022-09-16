{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.Language.ImpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.Imp
import Ceili.Name
import Ceili.TestUtil
import qualified Data.Map as Map
import qualified Data.Set as Set

name n = Name n 0
x = name "x"
y = name "y"
mkSt assocList = Map.fromList $ map (\(n,v) -> (Name n 0, v)) assocList

prog1 :: ImpProgram Integer
prog1 = impSeq [ impAsgn x $ ALit 5
               , impIf (BLt (AVar x) (ALit 0))
                   (impAsgn y $ ALit 0)
                   (impAsgn y $ ALit 1) ]

assertion :: String -> Assertion Integer
assertion assertionStr = case parseAssertion assertionStr of
  Left err        -> error $ "Bad assertion string: " ++ show err
  Right assertion -> assertion

runAndAssertEqual :: (Eq t, Show t) => t -> Ceili t -> IO ()
runAndAssertEqual expected task = do
  result <- runCeili emptyEnv task
  case result of
    Left err     -> assertFailure err
    Right actual -> assertEqual expected actual

test_forwardPT = do
  let expected = assertion
        "(or \
        \ (exists ((y!1 int)) \
        \   (and (= y 0)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (< x 0)))) \
        \ (exists ((y!2 int)) \
        \   (and (= y 1)      \
        \        (and (exists ((x!1 int)) (and (= x 5) true)) (not (< x 0))))))"
  actualEither <- runCeili (envImp prog1) $ impForwardPT () prog1 ATrue
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertEqual expected actual

test_backwardPT = do
  let post = Eq (Var y) (Num @Integer 1)
  let expected = assertion
        "(and \
        \  (=> (< 5 0) (= 0 1)) \
        \  (=> (not (< 5 0)) (= 1 1)))"
  actualEither <- runCeili (envImp prog1) $ impBackwardPT EmptyPieContextProvider prog1 post
  case actualEither of
    Left err     -> assertFailure $ show err
    Right actual -> assertEqual expected actual

test_mapNames = do
  let expected = impSeq [ impAsgn (Name "x!foo" 0) $ ALit 5
                        , impIf (BLt (AVar (Name "x!foo" 0)) (ALit 0))
                                (impAsgn (Name "y!foo" 0) $ ALit 0)
                                (impAsgn (Name "y!foo" 0) $ ALit 1) ]
  let actual = mapNames (\(Name n i) -> Name (n ++ "!foo") i) prog1
  assertEqual expected actual

evalImp = eval @Fuel @Integer @(ImpProgram Integer) @(ImpStep Integer)

test_evalImp_Skip = let
  st = mkSt [("x", 1), ("y", 2)]
  in runAndAssertEqual [st] $ evalImp InfiniteFuel st impSkip

test_evalImp_Asgn = let
  st = mkSt [("x", 1), ("y", 2)]
  prog = impAsgn x $ AAdd (AVar y) (ALit @Integer 3)
  expected = mkSt [("x", 5), ("y", 2)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_Seq = let
  st = mkSt [("x", 1), ("y", 2)]
  prog = impSeq [ impSkip
                , impAsgn y $ ALit 7
                , impAsgn x $ ASub (AVar y) (ALit @Integer 5)
                ]
  expected = mkSt [("x", 2), ("y", 7)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_IfTrue = let
  st = mkSt [("x", 1), ("y", -1)]
  prog = impIf (BGt (AVar x) (ALit @Integer 0))
               (impAsgn y $ ALit @Integer 1)
               (impAsgn y $ ALit @Integer 0)
  expected = mkSt [("x", 1), ("y", 1)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_IfFalse = let
  st = mkSt [("x", 1), ("y", -1)]
  prog = impIf (BLt (AVar x) (ALit @Integer 0))
               (impAsgn y $ ALit @Integer 1)
               (impAsgn y $ ALit @Integer 0)
  expected = mkSt [("x", 1), ("y", 0)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_WhileFalse = let
  st = mkSt [("x", 11), ("y", 0)]
  prog = impWhile (BLt (AVar x) (ALit @Integer 10))
                  (impSeq [ impAsgn y (ALit @Integer 1)
                          , impAsgn x $ AAdd (AVar x) (ALit @Integer 1)
                          ])
  expected = mkSt [("x", 11), ("y", 0)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_WhileLoop = let
  st = mkSt [("x", 0), ("y", 0)]
  prog = impWhile (BLt (AVar x) (ALit @Integer 10))
                  (impSeq [ impAsgn y (ALit @Integer 1)
                          , impAsgn x $ AAdd (AVar x) (ALit @Integer 1)
                          ])
  expected = mkSt [("x", 10), ("y", 1)]
  in runAndAssertEqual [expected] $ evalImp InfiniteFuel st prog

test_evalImp_InfiniteLoopRunsOutOfFuel = let
  prog = impWhile @Integer BTrue impSkip
  in runAndAssertEqual [] $ evalImp (Fuel 100) Map.empty prog

test_evalImp_slowMult = let
  st = mkSt [("x", 5), ("y", 7)]
  z  = name "z"
  c  = name "c"
  prog = impSeq [ impAsgn c $ AVar x
                , impAsgn z (ALit @Integer 0)
                , impWhile (BGt (AVar c) (ALit @Integer 0))
                           (impSeq [ impAsgn z $ AAdd (AVar z) (AVar y)
                                   , impAsgn c $ ASub (AVar c) (ALit @Integer 1)
                                   ])
                 ]
  expected = mkSt [("x", 5), ("y", 7), ("c", 0), ("z", 35)]
  in runAndAssertEqual [expected] $ evalImp (Fuel 100) st prog
