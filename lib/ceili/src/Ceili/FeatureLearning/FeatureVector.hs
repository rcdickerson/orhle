{-# LANGUAGE FlexibleContexts #-}

module Ceili.FeatureLearning.FeatureVector
  ( FeatureVector
  , createFV
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.ProgState
import Ceili.StatePredicate
import Data.Vector ( Vector, (!) )
import qualified Data.Vector as Vector

type FeatureVector = Vector Bool

createFV :: StatePredicate (Assertion t) t
         => Vector (Assertion t)
         -> Vector (ProgState t)
         -> Ceili (Vector FeatureVector)
createFV features tests =
  let fv = Vector.generate (Vector.length tests) $ \testIdx ->
           Vector.generate (Vector.length features) $ \featureIdx ->
           testState (features!featureIdx) (tests!testIdx)
  in (sequence $ Vector.map sequence fv) >>= pure . Vector.map (Vector.map (treatErrorsAs False))

treatErrorsAs :: Bool -> PredicateResult -> Bool
treatErrorsAs err result = case result of
  Accepted -> True
  Rejected -> False
  Error _  -> err
