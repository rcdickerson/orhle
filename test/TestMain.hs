{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} Orhle.AssertionTests
import {-@ HTF_TESTS @-} Orhle.Imp.ImpParserTests
import {-@ HTF_TESTS @-} Orhle.InlinerTests
import {-@ HTF_TESTS @-} Orhle.VerifierTests

main = htfMain htf_importedTests
