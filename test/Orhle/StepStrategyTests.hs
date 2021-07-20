{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.StepStrategyTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.CeiliEnv
import Orhle.SpecImp
import Orhle.StepStrategy


x = Name "x" 0

emptyProg = impSeq [] :: SpecImpProgram
incX = impAsgn x $ AAdd (AVar x) (ALit 1)

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
