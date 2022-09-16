{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Ceili.FeatureLearning.LinearInequalitiesTest(htf_thisModulesTests) where

import Test.Framework

import Ceili.Assertion
import Ceili.FeatureLearning.LinearInequalities
import Ceili.Name
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set

n :: String -> Name
n s = Name s 0

var :: String -> Arith Integer
var = Var . n

assertHasSameItems :: (Ord a, Show a) => Set a -> Set a -> IO ()
assertHasSameItems expected actual = let
  addToCount item counts = let current = Map.findWithDefault 0 item counts
                           in Map.insert item (current + 1) counts
  countItems = Set.foldr addToCount Map.empty
  in assertEqual (countItems expected) (countItems actual)

test_twoVarsNoLits = let
  names = Set.fromList [ n "x", n "y" ]
  expected = Set.fromList [ -- x
                            Lte (var "x") (Num $ -1)
                          , Lte (var "x") (Num 0)
                          , Lte (var "x") (Num 1)
                            -- -1 * x
                          , Lte (Mul[Num $ -1, (var "x")]) (Num $ -1)
                          , Lte (Mul[Num $ -1, (var "x")]) (Num 0)
                          , Lte (Mul[Num $ -1, (var "x")]) (Num 1)
                            -- y
                          , Lte (var "y") (Num $ -1)
                          , Lte (var "y") (Num 0)
                          , Lte (var "y") (Num 1)
                            -- -1 * y
                          , Lte (Mul[Num $ -1, (var "y")]) (Num $ -1)
                          , Lte (Mul[Num $ -1, (var "y")]) (Num 0)
                          , Lte (Mul[Num $ -1, (var "y")]) (Num 1)
                            -- x + y
                          , Lte (Add [var "x", var "y"]) (Num $ -1)
                          , Lte (Add [var "x", var "y"]) (Num 0)
                          , Lte (Add [var "x", var "y"]) (Num 1)
                            -- x + (-1 * y)
                          , Lte (Add [var "x", Mul[Num $ -1, var "y"]]) (Num $ -1)
                          , Lte (Add [var "x", Mul[Num $ -1, var "y"]]) (Num 0)
                          , Lte (Add [var "x", Mul[Num $ -1, var "y"]]) (Num 1)
                            -- (-1 * x) + y
                          , Lte (Add [Mul[Num $ -1, var "x"], var "y"]) (Num $ -1)
                          , Lte (Add [Mul[Num $ -1, var "x"], var "y"]) (Num 0)
                          , Lte (Add [Mul[Num $ -1, var "x"], var "y"]) (Num 1)
                            -- (-1 * x) + (-1 * y)
                          , Lte (Add [Mul[Num $ -1, var "x"], Mul[Num $ -1, var "y"]]) (Num $ -1)
                          , Lte (Add [Mul[Num $ -1, var "x"], Mul[Num $ -1, var "y"]]) (Num 0)
                          , Lte (Add [Mul[Num $ -1, var "x"], Mul[Num $ -1, var "y"]]) (Num 1)
                          ]
  in assertHasSameItems expected $ linearInequalities Set.empty names 2
