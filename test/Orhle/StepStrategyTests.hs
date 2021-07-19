{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.StepStrategyTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.CeiliEnv
import Orhle.SpecImp
import Orhle.StepStrategy

emptyProg = impSeq [] :: SpecImpProgram

test_backwardDisallowed = do
  result <- runCeili defaultEnv $ backwardDisallowed [] []
  case result of
    Left  _ -> return () -- Pass
    Right _ -> assertFailure "Unexpected success from backwardDisallowed strategy"
