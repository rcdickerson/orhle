{-# OPTIONS_GHC -F -pgmF htfpp #-}
{-# LANGUAGE TypeApplications #-}

module Ceili.Language.BExpTest(htf_thisModulesTests) where
import Test.Framework

import Ceili.Evaluation
import Ceili.Language.AExp
import Ceili.Language.BExp
import Ceili.Name
import qualified Data.Map as Map

mkSt assocList = Map.fromList $ map (\(n,v) -> (Name n 0, v)) assocList
name n = Name n 0

evalBExp = eval @() @Integer @(BExp Integer) @Bool ()

test_evalBExp_Lit = do
  assertEqual True  $ evalBExp Map.empty BTrue
  assertEqual False $ evalBExp Map.empty BFalse

test_evalBExp_Not = do
  assertEqual True  $ evalBExp Map.empty $ BNot BFalse
  assertEqual False $ evalBExp Map.empty $ BNot BTrue

test_evalBExp_Eq = do
  assertEqual True $ evalBExp
                     (mkSt [("x", 3), ("y", 3)])
                     (BEq (AVar $ name "x") (AVar $ name "y"))
  assertEqual False $ evalBExp
                     (mkSt [("x", 3), ("y", 4)])
                     (BEq (AVar $ name "x") (AVar $ name "y"))

test_evalBExp_MiscBExps = do
  assertEqual True $ evalBExp
                     (mkSt [("x", 3), ("y", 4)])
                     (BOr
                       (BEq (AVar $ name "x") (AVar $ name "y"))
                       (BGt (AAdd (AVar $ name "x") (ALit 5))
                            (AVar $ name "y")))
  assertEqual False $ evalBExp
                     (mkSt [("x", 3), ("y", 4)])
                     (BAnd
                       (BEq (AVar $ name "x") (AVar $ name "y"))
                       (BGt (AAdd (AVar $ name "x") (ALit 5))
                            (AVar $ name "y")))
