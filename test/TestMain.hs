{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} Orhle.CInvGenTests
import {-@ HTF_TESTS @-} Orhle.CValueTests
import {-@ HTF_TESTS @-} Orhle.SpecImpTests
import {-@ HTF_TESTS @-} Orhle.StepStrategyTests
import {-@ HTF_TESTS @-} Orhle.VerifierTests

main = htfMain htf_importedTests
