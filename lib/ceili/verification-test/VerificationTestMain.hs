{-# OPTIONS_GHC -F -pgmF htfpp #-}
module VerificationTestMain where

import Test.Framework

import {-@ HTF_TESTS @-} Ceili.FunImpVerificationTests
import {-@ HTF_TESTS @-} Ceili.ImpVerificationTests
import {-@ HTF_TESTS @-} Ceili.InvariantInference.PieVerificationTests

main = htfMain htf_importedTests
