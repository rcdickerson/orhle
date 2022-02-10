{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.DTLearn2
  ( LearnerContext(..)
  , learnSeparator
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, runStateT, get, put )
import qualified Data.List as List
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Map ( Map )
import qualified Data.Map as Map
import Prettyprinter

data Feature t = Feature { f_assertion     :: Assertion t
                         , f_rejectedBads  :: Set (ProgState t)
                         , f_acceptedGoods :: Set (ProgState t)
                         } deriving (Ord)
instance Eq t => Eq (Feature t)
  where f1 == f2 = (f_assertion f1) == (f_assertion f2)

data Clause t = Clause { c_features      :: [Feature t]
                       , c_rejectedBads  :: Set (ProgState t)
                       , c_acceptedGoods :: Set (ProgState t)
                       } deriving (Eq, Ord)

singletonClause :: Feature t -> Clause t
singletonClause feature = Clause [feature] (f_rejectedBads feature) (f_acceptedGoods feature)

c_size :: Clause t -> Int
c_size = length . c_features

-- Context that we get to keep across invocations of learnSeparator.
data LearnerContext t = LearnerContext { lctx_acceptsGoodCache :: Map (Assertion t) (Set (ProgState t))
                                       }

data SepCtx t = SepCtx { ctx_learnerContext :: LearnerContext t
                       , ctx_queue          :: FeatureQueue t
                       , ctx_features       :: [Feature t] -- Need to chuck useless features.
                       , ctx_badStates      :: Set (ProgState t)
                       , ctx_goodStates     :: Set (ProgState t)
                       , ctx_maxClauseSize  :: Int
                       }

type FeatureQueue t = Map Int (Set (Clause t))

peekQueue :: FeatureQueue t -> Maybe (Clause t)
peekQueue queue
  | Map.null queue = Nothing
  | otherwise =
      let (_, max) = Map.findMax queue
      in if Set.null max then Nothing else Just $ Set.findMax max

enqueue :: Ord t => (Clause t) -> FeatureQueue t -> FeatureQueue t
enqueue clause queue =
  let score = scoreClause clause
  in case Map.lookup score queue of
    Nothing  -> Map.insert score (Set.singleton clause) queue
    Just set -> Map.insert score (Set.insert clause set) queue

scoreClause :: Clause t -> Int
scoreClause clause = (Set.size $ c_rejectedBads clause)
             + (1000 * (Set.size $ c_acceptedGoods clause))

queueSize :: FeatureQueue t -> Int
queueSize = Map.foldr (\set count -> count + Set.size set) 0

type SepM t = StateT (SepCtx t) Ceili

getQueue :: SepM t (FeatureQueue t)
getQueue = get >>= pure . ctx_queue

getAgCache :: SepM t (Map (Assertion t) (Set (ProgState t)))
getAgCache = get >>= pure . lctx_acceptsGoodCache . ctx_learnerContext

putAgCache :: Map (Assertion t) (Set (ProgState t)) -> SepM t ()
putAgCache agCache = do
  SepCtx _ queue features badStates goodStates maxClauseSize <- get
  put $ SepCtx (LearnerContext agCache) queue features badStates goodStates maxClauseSize

getFeatures :: SepM t [Feature t]
getFeatures = get >>= pure . ctx_features

getBadStates :: SepM t (Set (ProgState t))
getBadStates = get >>= pure . ctx_badStates

getBadStatesList :: SepM t [ProgState t]
getBadStatesList = do
  badStates <- getBadStates
  pure . Set.toList $ badStates

getGoodStates :: SepM t (Set (ProgState t))
getGoodStates = get >>= pure . ctx_goodStates

getGoodStatesList :: SepM t [ProgState t]
getGoodStatesList = do
  goodStates <- getGoodStates
  pure . Set.toList $ goodStates

getMaxClauseSize :: SepM t Int
getMaxClauseSize = get >>= pure . ctx_maxClauseSize

putQueue :: (FeatureQueue t) -> SepM t ()
putQueue queue = do
  SepCtx lctx _ features badStates goodStates maxClauseSize <- get
  put $ SepCtx lctx queue features badStates goodStates maxClauseSize

popQueue :: SepM t (Maybe (Clause t))
popQueue = do
  queue <- getQueue
  let mMaxView = Map.maxViewWithKey queue
  case mMaxView of
    Nothing -> pure Nothing
    Just ((key, maxSet), queue') -> do
      let mMaxElt = Set.maxView maxSet
      case mMaxElt of
        Nothing -> do
          putQueue queue'
          pure Nothing
        Just (elt, maxSet') -> do
          putQueue $ Map.insert key maxSet' queue'
          pure $ Just elt

mergeQueue :: Ord t => Pretty t => (FeatureQueue t) -> SepM t ()
mergeQueue batch = do
  queue <- getQueue
  let newQueue = Map.unionWith Set.union queue batch
  let newQueueHead = case peekQueue newQueue of
                       Nothing -> "<empty>"
                       Just clause -> show . clauseToAssertion $ clause
  let batchHead = case peekQueue batch of
                       Nothing -> "<empty>"
                       Just clause -> show . clauseToAssertion $ clause
  lift . log_d $ "Appending " ++ (show $ queueSize batch) ++ " to queue, new size " ++ (show $ queueSize newQueue) ++ ". Head of queue: " ++ newQueueHead ++ ", head of batch: " ++ batchHead
  putQueue newQueue

learnSeparator :: ( Embeddable Integer t
                  , Ord t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  , SatCheckable t
                  )
               => Int
               -> Int
               -> (Set Name -> Int -> Set (Assertion t))
               -> LearnerContext t
               -> [ProgState t]
               -> [ProgState t]
               -> Ceili (LearnerContext t, Maybe (Assertion t))
learnSeparator maxClauseSize maxFeatureSize featureGen lctx rawBadStates rawGoodStates
  | null rawBadStates = pure (lctx, Just ATrue)
  | otherwise = do
      -- Add missing names to states. TODO: This might not be the best place for this.
      let names = Set.toList . Set.unions $ map namesIn rawBadStates
                                         ++ map namesIn rawGoodStates
      let prepareStates = map $ addMissingNames names
      let badStates = prepareStates rawBadStates
      let goodStates = prepareStates rawGoodStates
      -------
      (lctx', features) <- (prepareFeatures lctx badStates goodStates) . Set.toList $ featureGen (Set.fromList names) maxFeatureSize
      log_d $ "**** Prepared features"
      (lctx'', mSeparator) <- separatorSearch maxClauseSize features lctx' (Set.fromList badStates) (Set.fromList goodStates)
      case mSeparator of
        Nothing -> pure (lctx'', Nothing)
        Just separator -> pure (lctx'', Just . aOr $ map clauseToAssertion separator)

-- TODO: This is super jank.
prepareFeatures :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t )
                => LearnerContext t
                -> [ProgState t]
                -> [ProgState t]
                -> [Assertion t]
                -> Ceili (LearnerContext t, [Feature t])
prepareFeatures lctx _ _ [] = pure (lctx, [])
prepareFeatures lctx badStates goodStates (a:as) = do
  (_, rejectedBads) <- splitStates a badStates
  (lctx', rest) <- prepareFeatures lctx badStates goodStates as
  if null rejectedBads
    then pure (lctx', rest)
    else do
      (lctx'', acceptedGoods) <- lookupAcceptedGoods lctx' a goodStates
      if null acceptedGoods
        then pure (lctx'', rest)
        else
          let feature = Feature a (Set.fromList rejectedBads) acceptedGoods
          in pure (lctx'', feature:rest)

lookupAcceptedGoods :: ( Ord t
                       , StatePredicate (Assertion t) t
                       , Pretty t )
                    => LearnerContext t
                    -> Assertion t
                    -> [ProgState t]
                    -> Ceili (LearnerContext t, Set (ProgState t))
lookupAcceptedGoods lctx@(LearnerContext agCache) assertion goodStates = do
  let mResult = Map.lookup assertion agCache
  case mResult of
    Just result -> pure (lctx, result)
    Nothing -> do
      (acceptedGoodsList, _) <- splitStates assertion goodStates
      let acceptedGoods = Set.fromList acceptedGoodsList
      let agCache' = Map.insert assertion acceptedGoods agCache
      pure (LearnerContext agCache', acceptedGoods)

-- SepM version of the above function. This is obviously terrible.
findAcceptedGoods :: ( Ord t
                     , StatePredicate (Assertion t) t
                     , Pretty t )
                  => Assertion t
                  -> [ProgState t]
                  -> SepM t (Set (ProgState t))
findAcceptedGoods assertion customGoodStates = do
    -- (acceptedGoodsList, _) <- lift $ splitStates assertion customGoodStates
    -- let result = Set.fromList acceptedGoodsList
    -- pure result
  agCache <- getAgCache
  let mResult = Map.lookup assertion agCache
  case mResult of
    Just result -> pure result
    Nothing -> do
      (acceptedGoodsList, _) <- lift $ splitStates assertion customGoodStates
      let result = Set.fromList acceptedGoodsList
      let agCache' = Map.insert assertion result agCache
      putAgCache agCache'
      pure result

separatorSearch :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t
                   )
                => Int
                -> [Feature t]
                -> LearnerContext t
                -> Set (ProgState t)
                -> Set (ProgState t)
                -> Ceili (LearnerContext t, Maybe [Clause t])
separatorSearch maxClauseSize features lctx badStates goodStates = do
  let initQueue = foldr (\feature queue -> enqueue (singletonClause feature) queue) Map.empty features
  let context = SepCtx lctx initQueue features badStates goodStates maxClauseSize
  log_d $ "[DTLearn] Beginning clause search. " ++ (show $ Set.size badStates) ++ " bad states, " ++
    (show $ Set.size goodStates) ++ " good states, " ++ (show $ length features) ++ " features."
  (mClause, newContext) <- runStateT clauseSearch context
  let lctx' = ctx_learnerContext newContext
  case mClause of
    Nothing -> pure (lctx', Nothing)
    Just clause -> do
      log_d $ "**** Found clause: " ++ show (clauseToAssertion clause)
      let remainingGoods = Set.difference goodStates $ c_acceptedGoods clause
      if Set.null remainingGoods
        then pure (lctx', Just [clause])
        else do
          log_d $ "**** " ++ show (Set.size remainingGoods) ++ " remaining good states left"
          let filterGoods (Feature assertion rejectedBads acceptedGoods) =
                let goods' = Set.intersection acceptedGoods remainingGoods
                in if Set.null goods' then Nothing else Just $ Feature assertion rejectedBads goods'
          let features' = catMaybes $ map filterGoods features
          (lctx'', mNextSep) <- separatorSearch maxClauseSize features' lctx badStates remainingGoods
          case mNextSep of
            Nothing -> pure (lctx'', Nothing)
            Just rest -> pure (lctx'', Just $ clause:rest)

addMissingNames :: forall t. (Ord t, Embeddable Integer t) => [Name] -> ProgState t -> ProgState t
addMissingNames names progState = foldr
                                  (\name st -> if Map.member name st
                                    then st
                                    else Map.insert name (embed 0) st)
                                  progState names

splitStates :: forall t.
                 ( Ord t
                 , StatePredicate (Assertion t) t
                 )
              => Assertion t
              -> [ProgState t]
              -> Ceili ([ProgState t], [ProgState t])
splitStates assertion states = do
  let resultPairs state = do result <- testState assertion state; pure (state, result)
  evaluations <- sequence $ map resultPairs states
  let (accepted, rejected) = List.partition snd evaluations
  pure (map fst accepted, map fst rejected)

clauseSearch :: ( Ord t
                , StatePredicate (Assertion t) t
                , Pretty t
                ) => SepM t (Maybe (Clause t))
clauseSearch = do
  mCandidate <- popQueue
  case mCandidate of
    Nothing -> pure Nothing -- Queue is empty, we're done.
    Just candidate -> do
      mResult <- appendNextFeatures candidate
      case mResult of
        Nothing -> clauseSearch
        Just clause -> pure $ Just clause

appendNextFeatures :: ( Ord t
                      , StatePredicate (Assertion t) t
                      , Pretty t
                      )
                   => Clause t
                   -> SepM t (Maybe (Clause t))
appendNextFeatures candidate = do
  maxClauseSize <- getMaxClauseSize
  if c_size candidate >= maxClauseSize
    then pure Nothing
    else do
      features <- getFeatures
      resultOrBatch <- nextQueueBatch features candidate Map.empty
      case resultOrBatch of
        Right result -> pure $ Just result
        Left batch -> mergeQueue batch >> pure Nothing

nextQueueBatch :: ( Ord t
                  , StatePredicate (Assertion t) t
                  , Pretty t
                  )
               => [Feature t]
               -> Clause t
               -> FeatureQueue t
               -> SepM t (Either (FeatureQueue t) (Clause t))
nextQueueBatch [] _ batch = pure $ Left batch
nextQueueBatch (feature:rest) candidate batch = do
  finished <- clauseRejectsAllBads candidate
  if finished
    then pure $ Right candidate
    else do
      mCandidate' <- addFeature candidate feature
      case mCandidate' of
        Nothing -> nextQueueBatch rest candidate batch
        Just candidate' -> nextQueueBatch rest candidate (enqueue candidate' batch)
--      mCandidate' <- addFeature candidate feature
--      case mCandidate' of
        -- Nothing -> nextQueueBatch rest candidate batch
        -- Just candidate' -> do
        --   finished' <- clauseRejectsAllBads candidate'
        --   if finished'
        --     then pure $ Right candidate'
        --     else nextQueueBatch rest candidate (enqueue candidate' batch)

clauseRejectsAllBads :: Eq t => Clause t -> SepM t Bool
clauseRejectsAllBads clause = do
  badStates <- getBadStates
  pure $ (c_rejectedBads clause) == badStates

addFeature :: ( Ord t
              , StatePredicate (Assertion t) t
              , Pretty t
              )
           => Clause t
           -> Feature t
           -> SepM t (Maybe (Clause t))
addFeature clause feature = do
  let oldRejectedBads = c_rejectedBads clause
  if Set.isSubsetOf (f_rejectedBads feature) oldRejectedBads
    then pure Nothing
    else do
      let oldAcceptedGoods = (c_acceptedGoods clause)
      if False --Set.isSubsetOf (f_acceptedGoods feature) oldAcceptedGoods
        then pure Nothing
        else do
          let newAssertion = aAnd [f_assertion feature, clauseToAssertion clause]
          let newRejectedBads = Set.union (f_rejectedBads feature) oldRejectedBads
          newAcceptedGoods <- findAcceptedGoods newAssertion $ Set.toList oldAcceptedGoods
          if Set.null newAcceptedGoods
            then pure Nothing
            else pure . Just $ Clause (feature:c_features clause) newRejectedBads newAcceptedGoods

clauseToAssertion :: Clause t -> Assertion t
clauseToAssertion = aAnd . (map f_assertion) . c_features
