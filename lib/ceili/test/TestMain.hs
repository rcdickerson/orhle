{-# OPTIONS_GHC -F -pgmF htfpp #-}
module Main where

import Test.Framework
import {-@ HTF_TESTS @-} Ceili.AssertionTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.CollectionUtilTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.FeatureVectorTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.LinearInequalitiesTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.PACBooleanTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.PieTest
import {-@ HTF_TESTS @-} Ceili.FeatureLearning.SeparatorTest
import {-@ HTF_TESTS @-} Ceili.Language.AExpTest
import {-@ HTF_TESTS @-} Ceili.Language.AExpParserTest
import {-@ HTF_TESTS @-} Ceili.Language.BExpTest
import {-@ HTF_TESTS @-} Ceili.Language.FunImpParserTest
import {-@ HTF_TESTS @-} Ceili.Language.FunImpTest
import {-@ HTF_TESTS @-} Ceili.Language.ImpTest
import {-@ HTF_TESTS @-} Ceili.Language.ImpParserTest
import {-@ HTF_TESTS @-} Ceili.NameTest

main = htfMain htf_importedTests
