{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Orhle.SpecImpTests(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Name
import qualified Data.Set as Set
import Orhle.SpecImp


a  = Name "a" 0
a1 = Name "a" 1
b  = Name "b" 0
c  = Name "c" 0
c1 = Name "c" 1
r  = Name "r" 0
x  = Name "x" 0
y  = Name "y" 0
z  = Name "z" 0

a_v  = Var a
a1_v = Var a1
b_v  = Var b
r_v  = Var r
x_v  = Var x

env = defaultEnv $ Set.fromList [a, b, c, r, x, y, z]


-- test_specAtCallsite = do
--   let call = SpecCall "dummy_cid" [AVar b] [a]
--   let spec = Specification [x] [r] [c_i] ATrue (Eq r_v $ Add [x_v, Num 1])
--   result <- runCeili env $ specAtCallsite call spec
--   case result of
--     Left err -> assertFailure err
--     Right (Specification params retVars choiceVars pre post) -> do
--       assertEqual [x] params
--       assertEqual [r] retVars
--       assertEqual [c1_i] choiceVars
--       assertEqual ATrue pre
--       assertEqual (Eq a_v $ Add [b_v, Num 1]) post

-- test_specAtCallsite_assignToArg = do
--   let call = SpecCall "dummy_cid" [AVar a] [a]
--   let spec = Specification [x] [r] [c_i] ATrue (Eq r_v $ Add [x_v, Num 1])
--   result <- runCeili env $ specAtCallsite call spec
--   case result of
--     Left err -> assertFailure err
--     Right (Specification params retVars choiceVars pre post) -> do
--       assertEqual [x] params
--       assertEqual [r] retVars
--       assertEqual [c1_i] choiceVars
--       assertEqual ATrue pre
--       assertEqual (Eq a_v $ Add [a1_v, Num 1]) post
