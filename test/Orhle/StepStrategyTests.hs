{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.StepStrategyTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.CeiliEnv
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

env = mkEnv [ incX, incY, incZ
            , loop1, loop2, loop3 ]

toLoop :: SpecImpProgram -> ImpWhile SpecImpProgram
toLoop prog = case getLoop prog of
  Nothing -> error $ "Not a loop: " ++ show prog
  Just loop -> loop


test_backwardDisallowed = do
  result <- runCeili defaultEnv $ backwardDisallowed [] []
  case result of
    Left  _ -> return () -- Pass
    Right _ -> assertFailure "Unexpected success from backwardDisallowed strategy"

test_backwardWithFusion_emptySeqTreatedAsSkip =
  let expected = Step (ExistentialStatement impSkip) [incX] []
  in do
    result <- runCeili env $ backwardWithFusion [incX] [impSeq []]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_noProgramsReturnsNoSelectionFound =
  let expected = Step NoSelectionFound [] []
  in do
    result <- runCeili env $ backwardWithFusion [] []
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step


test_backwardWithFusion_emptyUniversalsPicksExistential =
  let expected = Step (ExistentialStatement incX) [] []
  in do
    result <- runCeili env $ backwardWithFusion [] [incX]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_emptyExistentialPicksUniversal =
  let expected = Step (UniversalStatement incX) [] []
  in do
    result <- runCeili env $ backwardWithFusion [incX] []
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_favorsExistential =
  let expected = Step (ExistentialStatement incX) [incX] []
  in do
    result <- runCeili env $ backwardWithFusion [incX] [incX]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_allLoopsInExistentialPicksUniversal =
  let expected = Step (UniversalStatement incY) [loop1] [impSeq [incX, loop2], loop3]
  in do
    result <- runCeili env $ backwardWithFusion [loop1, incY] [impSeq [incX, loop2], loop3]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_allLoopsInUniversalPicksExistential =
  let expected = Step (ExistentialStatement incY) [impSeq [incX, loop2], loop3] [loop1]
  in do
    result <- runCeili env $ backwardWithFusion [impSeq [incX, loop2], loop3] [loop1, incY]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_pickingUniversalPreservesRestOfSeq =
  let expected = Step (UniversalStatement incZ) [impSeq [incX, incY]] []
  in do
    result <- runCeili env $ backwardWithFusion [impSeq [incX, incY, incZ]] []
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_pickingExistentialPreservesRestOfSeq =
  let expected = Step (ExistentialStatement incZ) [] [impSeq [incX, incY]]
  in do
    result <- runCeili env $ backwardWithFusion [] [impSeq [incX, incY, incZ]]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

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
    result <- runCeili env $ backwardWithFusion aprogs eprogs
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step
