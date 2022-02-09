{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.DTLearn2
  ( learnSeparator
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import qualified Data.List as List
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Prettyprinter

data Feature t = Feature { f_assertion    :: Assertion t
                         , f_rejectedBads :: Set (ProgState t)
                         }
instance Eq t => Eq (Feature t)
  where f1 == f2 = (f_assertion f1) == (f_assertion f2)

data Clause t = Clause { c_features      :: [Feature t]
                       , c_rejectedBads  :: Set (ProgState t)
                       , c_acceptedGoods :: Set (ProgState t)
                       }

c_size :: Clause t -> Int
c_size = length . c_features

data SepCtx t = SepCtx { ctx_queue         :: [Clause t]
                       , ctx_features      :: [Feature t] -- Need to chuck useless features.
                       , ctx_badStates     :: Set (ProgState t)
                       , ctx_goodStates    :: Set (ProgState t)
                       , ctx_maxClauseSize :: Int
                       }

type SepM t = StateT (SepCtx t) Ceili

getQueue :: SepM t [Clause t]
getQueue = get >>= pure . ctx_queue

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

putQueue :: [Clause t] -> SepM t ()
putQueue queue = do
  SepCtx _ features badStates goodStates maxClauseSize <- get
  put $ SepCtx queue features badStates goodStates maxClauseSize

appendToQueue :: Pretty t => [Clause t] -> SepM t ()
appendToQueue batch = do
  queue <- getQueue
  let newQueue = queue ++ batch
  lift . log_d $ "Appending " ++ (show $ length batch) ++ " to queue, new size " ++ (show $ length newQueue) ++
    ". Head of queue: " ++
    (if null queue then "<empty>" else show . clauseToAssertion . head $ queue)
    ++ ", head of batch: " ++
    (if null batch then "<empty>" else show . clauseToAssertion . head $ batch)
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
               -> [ProgState t]
               -> [ProgState t]
               -> Ceili (Maybe (Assertion t))
learnSeparator maxClauseSize maxFeatureSize featureGen rawBadStates rawGoodStates
  | null rawBadStates = pure $ Just ATrue
  | otherwise = do
      -- Add missing names to states. TODO: This might not be the best place for this.
      let names = Set.toList . Set.unions $ map namesIn rawBadStates
                                         ++ map namesIn rawGoodStates
      let prepareStates = map $ addMissingNames names
      let badStates = Set.fromList $ prepareStates rawBadStates
      let goodStates = Set.fromList $ prepareStates rawGoodStates
      -------
      features <- (prepareFeatures $ Set.toList badStates) . Set.toList $ featureGen (Set.fromList names) maxFeatureSize
      log_d $ "**** Prepared features"
      mSeparator <- separatorSearch maxClauseSize features badStates goodStates
      case mSeparator of
        Nothing -> pure Nothing
        Just separator -> pure . Just . aOr $ map clauseToAssertion separator

-- TODO: This should be a catMaybes . sequence . map
prepareFeatures :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t )
                => [ProgState t]
                -> [Assertion t]
                -> Ceili [Feature t]
prepareFeatures _ [] = pure []
prepareFeatures badStates (a:as) = do
  (_, rejectedBads) <- splitStates a badStates
  rest <- prepareFeatures badStates as
  if null rejectedBads
    then pure rest
    else pure $ (Feature a $ Set.fromList rejectedBads):rest

separatorSearch :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t
                   )
                => Int
                -> [Feature t]
                -> Set (ProgState t)
                -> Set (ProgState t)
                -> Ceili (Maybe [Clause t])
separatorSearch maxClauseSize features badStates goodStates = do
  let emptyClause = Clause [] Set.empty goodStates
  mClause <- evalStateT clauseSearch (SepCtx [emptyClause] features badStates goodStates maxClauseSize)
  case mClause of
    Nothing -> pure Nothing
    Just clause -> do
      log_d $ "**** Found clause: " ++ show (clauseToAssertion clause)
      let remainingGoods = Set.difference goodStates $ c_acceptedGoods clause
      if Set.null remainingGoods
        then pure $ Just [clause]
        else do
          log_d $ "**** " ++ show (Set.size remainingGoods) ++ " remaining good states left"
          mNextSep <- separatorSearch maxClauseSize features badStates remainingGoods
          case mNextSep of
            Nothing -> pure Nothing
            Just rest -> pure . Just $ clause:rest

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
  queue <- getQueue
  case queue of
    [] -> pure Nothing
    (candidate:qTail) -> do
      putQueue qTail
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
      resultOrBatch <- nextQueueBatch features candidate []
      case resultOrBatch of
        Right result -> pure $ Just result
        Left batch -> appendToQueue batch >> pure Nothing

nextQueueBatch :: ( Ord t
                  , StatePredicate (Assertion t) t
                  , Pretty t
                  )
               => [Feature t]
               -> Clause t
               -> [Clause t]
               -> SepM t (Either [Clause t] (Clause t))
nextQueueBatch [] _ batch = pure $ Left batch
nextQueueBatch (feature:rest) candidate batch = do
  mCandidate' <- addFeature candidate feature
  case mCandidate' of
    Nothing -> nextQueueBatch rest candidate batch
    Just candidate' -> do
      finished <- clauseRejectsAllBads candidate'
      if finished
        then pure $ Right candidate'
        else nextQueueBatch rest candidate (candidate':batch)

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
  goodStates <- getGoodStatesList
  let oldRejectedBads = c_rejectedBads clause
  if Set.isSubsetOf (f_rejectedBads feature) oldRejectedBads
    then pure Nothing
    else do
      let newAssertion = aAnd [f_assertion feature, clauseToAssertion clause]
      let newRejectedBads = Set.union (f_rejectedBads feature) oldRejectedBads
      (newAcceptedGoodsList, _) <- lift $ splitStates newAssertion goodStates
      if null newAcceptedGoodsList
        then pure Nothing
        else do
          let newAcceptedGoods = Set.fromList newAcceptedGoodsList
          pure . Just $ Clause (feature:c_features clause) newRejectedBads newAcceptedGoods

clauseToAssertion :: Clause t -> Assertion t
clauseToAssertion = aAnd . (map f_assertion) . c_features
