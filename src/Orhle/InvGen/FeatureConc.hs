module Orhle.InvGen.FeatureConc
  ( Feature(..)
  , FeatureCache(..)
  , FeatureId
  , FeatureIdSet
  , fcAddBadState
  , fcAddFeature
  , fcClearBadStates
  , fcEmpty
  , fcFeaturesWhichAccept
  , fcFeaturesWhichReject
  , fcIncrementId
  , fcLookupFeature
  , fcLookupFeatures
  , fcRejectedBads
  , fcRemoveFeature
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Control.Monad ( filterM )
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import Data.Map ( Map )
import qualified Data.Map as Map
import Orhle.InvGen.StateConc
import Prettyprinter


--------------
-- Features --
--------------

type FeatureId = Int
type FeatureIdSet = IntSet

data Feature t = Feature
  { featId            :: FeatureId
  , featAssertion     :: Assertion t
  , featAcceptedGoods :: IntSet
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Feature t) where
  pretty (Feature _ assertion _) = pretty assertion


-------------------
-- Feature Cache --
-------------------

data FeatureCache t = FeatureCache
  { fcNextFeatureId      :: FeatureId
  , fcFeatureIds         :: FeatureIdSet
  , fcFeaturesById       :: Map FeatureId (Feature t)
  , fcRejectedByFeature  :: Map FeatureId BadStateIdSet
  , fcFeaturesByAccepted :: Map GoodStateId FeatureIdSet
  , fcFeaturesByRejected :: Map BadStateId FeatureIdSet
  }

fcEmpty :: FeatureCache t
fcEmpty = FeatureCache { fcNextFeatureId      = 0
                       , fcFeatureIds         = IntSet.empty
                       , fcFeaturesById       = Map.empty
                       , fcRejectedByFeature  = Map.empty
                       , fcFeaturesByAccepted = Map.empty
                       , fcFeaturesByRejected = Map.empty
                       }

fcClearBadStates :: FeatureCache t -> FeatureCache t
fcClearBadStates fc = fc { fcRejectedByFeature  = Map.empty
                         , fcFeaturesByRejected = Map.empty
                         }

fcIncrementId :: FeatureCache t -> (FeatureId, FeatureCache t)
fcIncrementId (FeatureCache nextId fids fById rejByFeat featByAcc featByRej) =
  (nextId, FeatureCache (nextId + 1) fids fById rejByFeat featByAcc featByRej)

fcAddFeature :: Ord t => Feature t -> BadStateIdSet -> FeatureCache t -> FeatureCache t
fcAddFeature feature rejected featureCache =
  let
    nextId                = fcNextFeatureId         featureCache
    featureIds            = fcFeatureIds            featureCache
    featuresById          = fcFeaturesById          featureCache
    rejectedByFeature     = fcRejectedByFeature     featureCache
    featsByAccepted       = fcFeaturesByAccepted featureCache
    featsByRejected       = fcFeaturesByRejected    featureCache
    featureId             = featId feature
    nextId'               = if featureId < nextId then nextId else featureId + 1
    featureIds'           = IntSet.insert featureId featureIds
    featuresById'         = Map.insert featureId feature featuresById
    rejectedByFeature'    = Map.insert featureId rejected rejectedByFeature
    featInsert stId stMap = case Map.lookup stId stMap of
                              Nothing  -> Map.insert stId (IntSet.singleton featureId)  stMap
                              Just set -> Map.insert stId (IntSet.insert featureId set) stMap
    featsByAccepted'      = foldr featInsert featsByAccepted $ IntSet.toList (featAcceptedGoods feature)
    featsByRejected'      = foldr featInsert featsByRejected    $ IntSet.toList rejected
  in
    if featureId `IntSet.member` featureIds
    then error $ "Feature ID already in use: " ++ (show featureId)
    else FeatureCache { fcNextFeatureId      = nextId'
                      , fcFeatureIds         = featureIds'
                      , fcFeaturesById       = featuresById'
                      , fcRejectedByFeature  = rejectedByFeature'
                      , fcFeaturesByAccepted = featsByAccepted'
                      , fcFeaturesByRejected = featsByRejected'
                      }

fcRemoveFeature :: Ord t => FeatureId -> FeatureCache t -> FeatureCache t
fcRemoveFeature featureId featureCache =
  let
    feature               = fcLookupFeature featureCache featureId
    rejected              = fcRejectedBads featureId featureCache
    featureIds            = fcFeatureIds            featureCache
    featuresById          = fcFeaturesById          featureCache
    rejectedByFeature     = fcRejectedByFeature     featureCache
    featsByAccepted       = fcFeaturesByAccepted featureCache
    featsByRejected       = fcFeaturesByRejected    featureCache
    featureIds'           = IntSet.delete featureId featureIds
    featuresById'         = Map.delete featureId featuresById
    rejectedByFeature'    = Map.delete featureId rejectedByFeature
    featDelete stId stMap = case Map.lookup stId stMap of
                              Nothing  -> stMap
                              Just set -> Map.insert stId (IntSet.delete featureId set) stMap
    featsByAccepted'      = foldr featDelete featsByAccepted $ IntSet.toList (featAcceptedGoods feature)
    featsByRejected'      = foldr featDelete featsByRejected $ IntSet.toList rejected
  in
    if featureId `IntSet.member` featureIds
    then error $ "Feature ID already in use: " ++ (show featureId)
    else FeatureCache { fcNextFeatureId      = fcNextFeatureId featureCache
                      , fcFeatureIds         = featureIds'
                      , fcFeaturesById       = featuresById'
                      , fcRejectedByFeature  = rejectedByFeature'
                      , fcFeaturesByAccepted = featsByAccepted'
                      , fcFeaturesByRejected = featsByRejected'
                      }

fcAddBadState :: BadStateId -> (Feature t -> Ceili Bool) -> FeatureCache t -> Ceili (FeatureCache t)
fcAddBadState stId testRejects fc = do
  let features = Map.elems $ fcFeaturesById fc
  rejectingFeatures <- filterM testRejects features
  let rejectingIds = map featId rejectingFeatures
  pure $ foldr (markRejected stId) fc rejectingIds

markRejected :: BadStateId -> FeatureId -> FeatureCache t -> FeatureCache t
markRejected stId featureId fc =
  let
    rbf      = fcRejectedByFeature  fc
    fbr      = fcFeaturesByRejected fc
  in fc { fcRejectedByFeature  = case Map.lookup featureId rbf of
                                   Nothing  -> Map.insert featureId (IntSet.singleton stId)  rbf
                                   Just set -> Map.insert featureId (IntSet.insert stId set) rbf
        , fcFeaturesByRejected = case Map.lookup stId fbr of
                                   Nothing  -> Map.insert stId (IntSet.singleton featureId)  fbr
                                   Just set -> Map.insert stId (IntSet.insert featureId set) fbr
        }

fcLookupFeature :: FeatureCache t -> FeatureId -> Feature t
fcLookupFeature fc featureId = case Map.lookup featureId $ fcFeaturesById fc of
  Nothing      -> error $ "Feature ID not found: " ++ show featureId
  Just feature -> feature

fcLookupFeatures :: FeatureCache t -> [FeatureId] -> [Feature t]
fcLookupFeatures fc = map $ fcLookupFeature fc

fcFeaturesWhichAccept :: Ord t => [GoodStateId] -> FeatureCache t -> [FeatureIdSet]
fcFeaturesWhichAccept states cache =
  case states of
    [] -> []
    (s:ss) -> case Map.lookup s (fcFeaturesByAccepted cache) of
      Nothing -> fcFeaturesWhichAccept ss cache
      Just features -> features:(fcFeaturesWhichAccept ss cache)

fcFeaturesWhichReject :: Ord t => [BadStateId] -> FeatureCache t -> [FeatureIdSet]
fcFeaturesWhichReject states cache =
  case states of
    [] -> []
    (s:ss) -> case Map.lookup s (fcFeaturesByRejected cache) of
      Nothing -> fcFeaturesWhichReject ss cache
      Just features -> features:(fcFeaturesWhichReject ss cache)


fcRejectedBads :: Ord t => FeatureId -> FeatureCache t -> BadStateIdSet
fcRejectedBads feature cache =
  case Map.lookup feature (fcRejectedByFeature cache) of
    Nothing       -> IntSet.empty
    Just rejected -> rejected
