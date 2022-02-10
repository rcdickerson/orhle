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
data LearnerContext t = LearnerContext { lctx_features     :: Maybe [Feature t]
                                       , lctx_queue        :: Maybe (FeatureQueue t)
                                       , lctx_lastSeenBads :: Set (ProgState t)
                                       }

data SepCtx t = SepCtx { ctx_queue          :: FeatureQueue t
                       , ctx_features       :: [Feature t]
                       , ctx_badStates      :: Set (ProgState t)
                       , ctx_goodStates     :: Set (ProgState t)
                       , ctx_maxClauseSize  :: Int
                       }

type FeatureQueue t = Map Int (Set (Clause t))

peekQueue :: FeatureQueue t -> Maybe (Clause t)
peekQueue queue
  | Map.null queue = Nothing
  | otherwise =
      let (_, maxElt) = Map.findMax queue
      in if Set.null maxElt then Nothing else Just $ Set.findMax maxElt

popQueue :: FeatureQueue t -> (Maybe (Clause t), FeatureQueue t)
popQueue queue = do
  let mMaxView = Map.maxViewWithKey queue
  case mMaxView of
    Nothing -> (Nothing, queue)
    Just ((key, maxSet), queue') -> do
      let mMaxElt = Set.maxView maxSet
      case mMaxElt of
        Nothing -> (Nothing, queue')
        Just (elt, maxSet') -> (Just elt, Map.insert key maxSet' queue')

enqueue :: Ord t => Clause t -> FeatureQueue t -> FeatureQueue t
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

getFeatures :: SepM t [Feature t]
getFeatures = get >>= pure . ctx_features

getBadStates :: SepM t (Set (ProgState t))
getBadStates = get >>= pure . ctx_badStates

getGoodStates :: SepM t (Set (ProgState t))
getGoodStates = get >>= pure . ctx_goodStates

getMaxClauseSize :: SepM t Int
getMaxClauseSize = get >>= pure . ctx_maxClauseSize

putQueue :: (FeatureQueue t) -> SepM t ()
putQueue queue = do
  SepCtx _ features badStates goodStates maxClauseSize <- get
  put $ SepCtx queue features badStates goodStates maxClauseSize

sPopQueue :: SepM t (Maybe (Clause t))
sPopQueue = do
  queue <- getQueue
  let (elt, queue') = popQueue queue
  putQueue queue'
  pure elt

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
  lift . log_d $ "Appending " ++ (show $ queueSize batch) ++ " to queue, new size " ++ (show $ queueSize newQueue) ++
    ". Head of queue: " ++ newQueueHead ++ ", head of batch: " ++ batchHead
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
      let badStatesList = prepareStates rawBadStates
      let badStates = Set.fromList badStatesList
      let goodStatesList = prepareStates rawGoodStates
      let goodStates = Set.fromList goodStatesList
      -------
      features <- case lctx_features lctx of
        Just cache -> updateFeatures (lctx_lastSeenBads lctx) badStates cache
        Nothing -> do
          let rawFeatures = Set.toList $ featureGen (Set.fromList names) maxFeatureSize
          prepareFeatures badStatesList goodStatesList rawFeatures

      queue <- case lctx_queue lctx of
        Just cache -> updateQueue (lctx_lastSeenBads lctx) badStates cache
        Nothing -> pure $ foldr enqueue Map.empty $ map singletonClause features

      (queue', mSeparator) <- separatorSearch maxClauseSize features queue badStates goodStates

      let lctx' = LearnerContext (Just features) (Just queue') badStates
      case mSeparator of
        Nothing -> pure (lctx', Nothing)
        Just separator -> pure (lctx', Just . aOr $ map clauseToAssertion separator)

updateFeatures :: ( Ord t
                  , StatePredicate (Assertion t) t
                  )
               => Set (ProgState t)
               -> Set (ProgState t)
               -> [Feature t]
               -> Ceili [Feature t]
updateFeatures oldBadStates newBadStates features = do
  let badsToAdd = Set.toList $ Set.difference newBadStates oldBadStates
  let rejects assertion state = do
        result <- testState assertion state
        pure $ if result then Nothing else Just state
  let updateFeature (Feature assertion bads goods) = do
        mBads <- sequence $ map (rejects assertion) badsToAdd
        let newBads = Set.union bads (Set.fromList $ catMaybes mBads)
        pure $ Feature assertion newBads goods
  sequence $ map updateFeature features

updateQueue :: ( Ord t
               , StatePredicate (Assertion t) t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> FeatureQueue t
            -> Ceili (FeatureQueue t)
updateQueue oldBadStates newBadStates queue = do
  -- TODO: Cleanup duplication
  let badsToAdd = Set.toList $ Set.difference newBadStates oldBadStates
  let rejects assertion state = do
        result <- testState assertion state
        pure $ if result then Nothing else Just state
  let updateFeature (Feature assertion bads goods) = do
        mBads <- sequence $ map (rejects assertion) badsToAdd
        let newBads = Set.union bads (Set.fromList $ catMaybes mBads)
        pure $ Feature assertion newBads goods
  let updateClause (Clause features _ goods) = do
        features' <- sequence $ map updateFeature features
        let bads' = Set.unions $ map f_rejectedBads features'
        pure $ Clause features' bads' goods
  let queueList = foldr (++) [] $ map Set.toList $ Map.elems queue
  queueList' <- sequence $ map updateClause queueList
  pure $ foldr enqueue Map.empty queueList'

prepareFeatures :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t )
                => [ProgState t]
                -> [ProgState t]
                -> [Assertion t]
                -> Ceili [Feature t]
prepareFeatures _ _ [] = pure []
prepareFeatures badStates goodStates (a:as) = do
  (_, rejectedBads) <- splitStates a badStates
  rest <- prepareFeatures badStates goodStates as
  if null rejectedBads
    then pure rest
    else do
      acceptedGoods <- lookupAcceptedGoods a goodStates
      if null acceptedGoods
        then pure rest
        else
          let feature = Feature a (Set.fromList rejectedBads) acceptedGoods
          in pure (feature:rest)

lookupAcceptedGoods :: ( Ord t
                       , StatePredicate (Assertion t) t
                       , Pretty t )
                    => Assertion t
                    -> [ProgState t]
                    -> Ceili (Set (ProgState t))
lookupAcceptedGoods assertion goodStates = do
  (acceptedGoodsList, _) <- splitStates assertion goodStates
  let acceptedGoods = Set.fromList acceptedGoodsList
  pure acceptedGoods

separatorSearch :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t
                   )
                => Int
                -> [Feature t]
                -> FeatureQueue t
                -> Set (ProgState t)
                -> Set (ProgState t)
                -> Ceili (FeatureQueue t, Maybe [Clause t])
separatorSearch maxClauseSize features queue badStates goodStates = do
  let context = SepCtx queue features badStates goodStates maxClauseSize
  log_d $ "[DTLearn] Beginning clause search. " ++ (show $ Set.size badStates) ++ " bad states, " ++
    (show $ Set.size goodStates) ++ " good states, " ++ (show $ length features) ++ " features."
  (mClause, newContext) <- runStateT clauseSearch context
  let queue' = ctx_queue newContext
  case mClause of
    Nothing -> pure (queue', Nothing)
    Just clause -> do
      log_d $ "**** Found clause: " ++ show (clauseToAssertion clause)
      let remainingGoods = Set.difference goodStates $ c_acceptedGoods clause
      if Set.null remainingGoods
        then pure (queue', Just [clause])
        else do
          log_d $ "**** " ++ show (Set.size remainingGoods) ++ " remaining good states left"
          let filterGoods (Feature assertion rejectedBads acceptedGoods) =
                let goods' = Set.intersection acceptedGoods remainingGoods
                in if Set.null goods' then Nothing else Just $ Feature assertion rejectedBads goods'
          let features' = catMaybes $ map filterGoods features
          (lctx'', mNextSep) <- separatorSearch maxClauseSize features' queue' badStates remainingGoods
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
  mCandidate <- sPopQueue
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
  goodStates <- getGoodStates
  let oldRejectedBads = c_rejectedBads clause
  if Set.isSubsetOf (f_rejectedBads feature) oldRejectedBads
    then pure Nothing
    else do
      if Set.null $ Set.intersection (f_acceptedGoods feature) goodStates
        then pure Nothing
        else do
          let newAssertion = aAnd [f_assertion feature, clauseToAssertion clause]
          let newRejectedBads = Set.union (f_rejectedBads feature) oldRejectedBads
          newAcceptedGoods <- lift $ lookupAcceptedGoods newAssertion $ Set.toList goodStates
          if Set.null newAcceptedGoods
            then pure Nothing
            else pure . Just $ Clause (feature:c_features clause) newRejectedBads newAcceptedGoods

clauseToAssertion :: Clause t -> Assertion t
clauseToAssertion = aAnd . (map f_assertion) . c_features
