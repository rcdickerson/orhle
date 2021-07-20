{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.StepStrategyTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.CeiliEnv
import Orhle.SpecImp
import Orhle.StepStrategy


x = Name "x" 0
y = Name "y" 0
z = Name "z" 0

emptyProg = impSeq [] :: SpecImpProgram
incX = impAsgn x $ AAdd (AVar x) (ALit 1)
incY = impAsgn y $ AAdd (AVar y) (ALit 1)
incZ = impAsgn z $ AAdd (AVar z) (ALit 1)
loop1 = impWhile (BLt (AVar x) (ALit 10)) incX
loop2 = impWhile (BLt (AVar y) (ALit 10)) incY
loop3 = impWhile (BLt (AVar z) (ALit 10)) incZ

test_backwardDisallowed = do
  result <- runCeili defaultEnv $ backwardDisallowed [] []
  case result of
    Left  _ -> return () -- Pass
    Right _ -> assertFailure "Unexpected success from backwardDisallowed strategy"

test_backwardWithFusion_emptyUniversalsPicksExistential =
  let expected = Step (ExistentialStatement incX) [] []
  in do
    result <- runCeili (mkEnv incX) $ backwardWithFusion [] [incX]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_emptyExistentialPicksUniversal =
  let expected = Step (UniversalStatement incX) [] []
  in do
    result <- runCeili (mkEnv incX) $ backwardWithFusion [incX] []
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_favorsExistential =
  let expected = Step (ExistentialStatement incX) [incX] []
  in do
    result <- runCeili (mkEnv incX) $ backwardWithFusion [incX] [incX]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step

test_backwardWithFusion_allLoopsInExistentialPicksUniversal =
  let expected = Step (UniversalStatement incY) [loop1] [impSeq [incX, loop2], loop3]
  in do
    result <- runCeili (mkEnv incX) $ backwardWithFusion [loop1, incY] [impSeq [incX, loop2], loop3]
    case result of
      Left err -> assertFailure err
      Right step -> assertEqual expected step
