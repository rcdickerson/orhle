{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.StepStrategyTests(htf_thisModulesTests) where

import Test.Framework
import Orhle.TestUtil

import Ceili.CeiliEnv
import Ceili.Name
import qualified Data.Set as Set
import Orhle.SpecImp
import Orhle.StepStrategy


x = Name "x" 0
y = Name "y" 0
z = Name "z" 0

incX = impAsgn x $ AAdd (AVar x) (ALit 1)
incY = impAsgn y $ AAdd (AVar y) (ALit 1)
incZ = impAsgn z $ AAdd (AVar z) (ALit 1)
loop1 = impWhile (BLt (AVar x) (ALit 10)) incX
loop2 = impWhile (BLt (AVar y) (ALit 10)) incY
loop3 = impWhile (BLt (AVar z) (ALit 10)) incZ

names = namesIn [ incX, incY, incZ, loop1, loop2, loop3 ]

toLoop :: SpecImpProgram Integer -> ImpWhile Integer (SpecImpProgram Integer)
toLoop prog = case getLoop prog of
  Nothing -> error $ "Not a loop: " ++ show prog
  Just loop -> loop


test_backwardDisallowed = do
  solver <- mkSolver
  let env = defaultEnv solver Set.empty
  result <- runCeili env $ backwardDisallowed [] []
  case result of
    Left  _ -> return () -- Pass
    Right _ -> assertFailure "Unexpected success from backwardDisallowed strategy"

test_backwardWithFusion_emptySeqTreatedAsSkip =
  let expected = Step (ExistentialStatement impSkip) [incX] []
  in do
    actual <- evalCeili names $ backwardWithFusion [incX] [impSeq []]
    assertEqual expected actual

test_backwardWithFusion_noProgramsReturnsNoSelectionFound =
  let expected = Step @Integer NoSelectionFound [] []
  in do
    actual <- evalCeili names $ backwardWithFusion [] []
    assertEqual expected actual


test_backwardWithFusion_emptyUniversalsPicksExistential =
  let expected = Step (ExistentialStatement incX) [] []
  in do
    actual <- evalCeili names $ backwardWithFusion [] [incX]
    assertEqual expected actual

test_backwardWithFusion_emptyExistentialPicksUniversal =
  let expected = Step (UniversalStatement incX) [] []
  in do
    actual <- evalCeili names $ backwardWithFusion [incX] []
    assertEqual expected actual

test_backwardWithFusion_favorsExistential =
  let expected = Step (ExistentialStatement incX) [incX] []
  in do
    actual <- evalCeili names $ backwardWithFusion [incX] [incX]
    assertEqual expected actual

test_backwardWithFusion_allLoopsInExistentialPicksUniversal =
  let expected = Step (UniversalStatement incY) [loop1] [impSeq [incX, loop2], loop3]
  in do
    actual <- evalCeili names $ backwardWithFusion [loop1, incY] [impSeq [incX, loop2], loop3]
    assertEqual expected actual

test_backwardWithFusion_allLoopsInUniversalPicksExistential =
  let expected = Step (ExistentialStatement incY) [impSeq [incX, loop2], loop3] [loop1]
  in do
    actual <- evalCeili names $ backwardWithFusion [impSeq [incX, loop2], loop3] [loop1, incY]
    assertEqual expected actual

test_backwardWithFusion_pickingUniversalPreservesRestOfSeq =
  let expected = Step (UniversalStatement incZ) [impSeq [incX, incY]] []
  in do
    actual <- evalCeili names $ backwardWithFusion [impSeq [incX, incY, incZ]] []
    assertEqual expected actual

test_backwardWithFusion_pickingExistentialPreservesRestOfSeq =
  let expected = Step (ExistentialStatement incZ) [] [impSeq [incX, incY]]
  in do
    actual <- evalCeili names $ backwardWithFusion [] [impSeq [incX, incY, incZ]]
    assertEqual expected actual

test_backwardWithFusion_allLoopsPicksFusion =
  let
    aprogs = [ impSeq [incX, loop1]
             , loop1
             ]
    eprogs = [ impSeq [incY, loop2]
             , loop2
             ]
    expected = Step (LoopFusion [toLoop loop1, toLoop loop1]
                                [toLoop loop2, toLoop loop2])
                    [impSeq [incX]]
                    [impSeq [incY]]
  in do
    actual <- evalCeili names $ backwardWithFusion aprogs eprogs
    assertEqual expected actual
