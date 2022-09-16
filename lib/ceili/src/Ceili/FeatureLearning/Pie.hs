{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- An implementation of the core PIE algorithm from
-- "Data-driven precondition inference with learned features"
-- Padhi, Saswat, Rahul Sharma, and Todd Millstein
-- ACM SIGPLAN Notices 51.6 (2016): 42-56.
-- http://web.cs.ucla.edu/~todd/research/pldi16.pdf

module Ceili.FeatureLearning.Pie
  ( getConflict
  , pie
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.FeatureLearning.FeatureVector
import qualified Ceili.FeatureLearning.PACBoolean as BL
import qualified Ceili.FeatureLearning.Separator as SL
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Data.Maybe ( isJust )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Vector ( Vector )
import qualified Data.Vector as Vector
import Prettyprinter

type CandidateGenerator t = Set Name -> Int -> Set (Assertion t)

pie :: ( Embeddable Integer t
       , Ord t
       , Pretty t
       , StatePredicate (Assertion t) t )
    => Set (Assertion t)
    -> CandidateGenerator t
    -> [ProgState t]
    -> [ProgState t]
    -> Ceili (Maybe (Assertion t))
pie features candidates badTests goodTests =
  let toVec = Vector.fromList . Set.toList
  in pie' (toVec features) candidates (Vector.fromList badTests) (Vector.fromList goodTests)

pie' :: ( Embeddable Integer t
        , Ord t
        , Pretty t
        , StatePredicate (Assertion t) t )
    => Vector (Assertion t)
    -> CandidateGenerator t
    -> Vector (ProgState t)
    -> Vector (ProgState t)
    -> Ceili (Maybe (Assertion t))
pie' features candidates badTests goodTests = do
  log_d $ "[PIE] Beginning PIE pass with features: " ++ show features
  negFV <- createFV features badTests
  posFV <- createFV features goodTests
  case getConflict negFV posFV badTests goodTests of
    Just (xBad, xGood) -> do
      mNewFeature <- findAugmentingFeature candidates (Vector.take 8 xBad) (Vector.take 8 xGood)
      case mNewFeature of
        Nothing         -> return Nothing
        Just newFeature -> pie' (Vector.cons newFeature features) candidates badTests goodTests
    Nothing -> BL.learnBoolExpr features negFV posFV >>= return . Just

getConflict :: Vector FeatureVector
            -> Vector FeatureVector
            -> Vector (ProgState t)
            -> Vector (ProgState t)
            -> Maybe (Vector (ProgState t), Vector (ProgState t))
getConflict negFVs posFVs badTests goodTests = do
  conflict <- findConflict negFVs posFVs
  let negIndices = Vector.findIndices (== conflict) negFVs
  let posIndices = Vector.findIndices (== conflict) posFVs
  return (Vector.backpermute badTests negIndices, Vector.backpermute goodTests posIndices)

findConflict :: Vector FeatureVector -> Vector FeatureVector -> Maybe (Vector Bool)
findConflict negFVs posFVs = Vector.find (\pos -> isJust $ Vector.find (== pos) negFVs) posFVs

findAugmentingFeature :: ( Embeddable Integer t
                         , Ord t
                         , Pretty s
                         , Pretty t
                         , StatePredicate (Assertion t) s )
                      => CandidateGenerator t
                      -> Vector (ProgState s)
                      -> Vector (ProgState s)
                      -> Ceili (Maybe (Assertion t))
findAugmentingFeature candidateGenerator xBad xGood = do
  let maxFeatureSize = 4 -- TODO: Don't hardcode max feature size
  let (badTests, goodTests) = (Vector.toList xBad, Vector.toList xGood)
  let names = Set.union (namesIn badTests) (namesIn goodTests)
  let candidates = candidateGenerator names
  mNewFeature <- SL.findSeparator maxFeatureSize candidates badTests goodTests
  case mNewFeature of
    Just newFeature -> do
      return $ Just newFeature
    Nothing -> do
      case (Vector.length xBad < 2, Vector.length xGood < 2) of
        (True, True) -> log_d "[PIE] Single conflict has no separating feature, giving up"
                        >> return Nothing
        (True, _)    -> log_d "[PIE] Reducing conflict set in good tests"
                        >> findAugmentingFeature candidateGenerator xBad (halve xGood)
        _            -> log_d "[PIE] Reducing conflict set in bad tests"
                        >> findAugmentingFeature candidateGenerator (halve xBad) xGood

halve :: Vector a -> Vector a
halve vec =
  let len = Vector.length vec
  in Vector.drop (max (len `quot` 2) 1) vec
