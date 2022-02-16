{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.DTLearn2
  ( LearnerContext(..)
  , emptyLearnerContext
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

-- Context that we get to keep across invocations of learnSeparator.
data LearnerContext t = LearnerContext { lctx_unusedFeatures :: Maybe [Assertion t]
                                       , lctx_usedFeatures   :: Maybe [Feature t]
                                       , lctx_queue          :: Maybe (DTLQueue t)
                                       , lctx_lastSeenBads   :: Set (ProgState t)
                                       }

emptyLearnerContext :: LearnerContext t
emptyLearnerContext = LearnerContext Nothing Nothing Nothing Set.empty

-- The cost function for queue entries.
entryScore :: DTLQueueEntry t -> Int
entryScore (DTLQueueEntry clauses features unrejectedBads unacceptedGoods) =
  if Set.null unacceptedGoods && Set.null unrejectedBads
  then fromIntegral (maxBound :: Int)
  else let
    unrejectedBadsScore  = -1 * Set.size unrejectedBads
    unacceptedGoodsScore = -100 * Set.size unacceptedGoods
    clauseSizeScore      = -10 * length clauses
    featuresSizeScore    = -1 * length features
  in unrejectedBadsScore + unacceptedGoodsScore + clauseSizeScore + featuresSizeScore

--------------
-- Features --
--------------
data Feature t = Feature { f_assertion     :: Assertion t
                         , f_rejectedBads  :: Set (ProgState t)
                         , f_acceptedGoods :: Set (ProgState t)
                         } deriving (Ord)

instance Eq t => Eq (Feature t)
  where f1 == f2 = (f_assertion f1) == (f_assertion f2)


-------------
-- Clauses --
-------------
data Clause t = Clause { c_features      :: [Feature t]
                       , c_rejectedBads  :: Set (ProgState t)
                       , c_acceptedGoods :: Set (ProgState t)
                       } deriving (Eq, Ord)

------------
-- Queues --
------------

type DTLQueue t = Map Int (Set (DTLQueueEntry t))
data DTLQueueEntry t = DTLQueueEntry { qe_clauses         :: [Clause t]
                                     , qe_candidate       :: [Feature t]
                                     , qe_unrejectedBads  :: Set (ProgState t)
                                     , qe_unacceptedGoods :: Set (ProgState t)
                                     } deriving (Eq, Ord)

qPeek :: DTLQueue t -> Maybe (DTLQueueEntry t)
qPeek queue
  | Map.null queue = Nothing
  | otherwise =
      let (_, maxElt) = Map.findMax queue
      in if Set.null maxElt then Nothing else Just $ Set.findMax maxElt

qPop :: DTLQueue t -> (Maybe (DTLQueueEntry t), DTLQueue t)
qPop queue = do
  let mMaxView = Map.maxViewWithKey queue
  case mMaxView of
    Nothing -> (Nothing, queue)
    Just ((key, maxSet), queue') ->
      let mMaxElt = Set.maxView maxSet
      in case mMaxElt of
        Nothing -> (Nothing, queue')
        Just (elt, maxSet') ->
          if Set.null maxSet'
          then (Just elt, queue')
          else (Just elt, Map.insert key maxSet' queue')

qInsert :: Ord t => DTLQueueEntry t -> DTLQueue t -> DTLQueue t
qInsert entry queue =
  let score = entryScore entry
  in case Map.lookup score queue of
    Nothing  -> Map.insert score (Set.singleton entry) queue
    Just set -> Map.insert score (Set.insert entry set) queue

qSize :: DTLQueue t -> Int
qSize = Map.foldr (\set count -> count + Set.size set) 0


-----------------------------
-- Separator Learner Monad --
-----------------------------

data SepCtx t = SepCtx { ctx_queue         :: DTLQueue t
                       , ctx_features      :: [Feature t]
                       , ctx_maxClauseSize :: Int
                       }

type SepM t = StateT (SepCtx t) Ceili

getQueue :: SepM t (DTLQueue t)
getQueue = get >>= pure . ctx_queue

getQueueSize :: SepM t Int
getQueueSize = getQueue >>= pure . qSize

getFeatures :: SepM t [Feature t]
getFeatures = get >>= pure . ctx_features

getMaxClauseSize :: SepM t Int
getMaxClauseSize = get >>= pure . ctx_maxClauseSize

putQueue :: (DTLQueue t) -> SepM t ()
putQueue queue = do
  SepCtx _ features maxClauseSize <- get
  put $ SepCtx queue features maxClauseSize

dequeue :: SepM t (Maybe (DTLQueueEntry t))
dequeue = do
  queue <- getQueue
  let (elt, queue') = qPop queue
  putQueue queue'
  pure elt

enqueue :: Ord t => DTLQueueEntry t -> SepM t ()
enqueue entry = do
  queue <- getQueue
  putQueue $ qInsert entry queue


-------------
-- Learner --
-------------

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
  | Set.size (Set.fromList rawBadStates) < length rawBadStates = throwError "Duplicate bad states" -- TODO: Remove
  | otherwise = do
      -- Add missing names to states. TODO: This might not be the best place for this.
      let names = Set.toList . Set.unions $ map namesIn rawBadStates
                                         ++ map namesIn rawGoodStates
      let prepareStates  = map $ addMissingNames names
      let badStatesList  = prepareStates rawBadStates
      let goodStatesList = prepareStates rawGoodStates
      let badStates      = Set.fromList badStatesList
      let goodStates     = Set.fromList goodStatesList
      let oldBadStates   = lctx_lastSeenBads lctx
      -------

      (unusedFeatures, usedFeatures, newlyUsedFeatures) <- case (lctx_unusedFeatures lctx, lctx_usedFeatures lctx) of
        (Nothing, Nothing) -> do
          let rawFeatures = Set.toList $ featureGen (Set.fromList names) maxFeatureSize
          log_d $ "[DTLearn] " ++ (show $ length rawFeatures) ++ " initial features."
          (unused, used) <- prepareFeatures badStatesList goodStatesList rawFeatures
          pure (unused, used, used)
        (Nothing, Just used) -> do
          updated <- updateFeatures (lctx_lastSeenBads lctx) badStates used
          pure ([], updated, [])
        (Just unused, Nothing) -> do
          (unused', used) <- prepareFeatures badStatesList goodStatesList unused
          pure (unused', used, used)
        (Just unused, Just used) -> do
          updated <- updateFeatures (lctx_lastSeenBads lctx) badStates used
          (unused', newlyUsed) <- prepareFeatures badStatesList goodStatesList unused
          pure (unused', updated ++ newlyUsed, newlyUsed)

      initialQueue <- case lctx_queue lctx of
        Just q  -> updateQueue oldBadStates badStates q
        Nothing -> pure Map.empty
      let queue = foldr qInsert initialQueue $ map (featureToEntry badStates goodStates) newlyUsedFeatures

      log_d $ "[DTLearn] Beginning separator search. " ++
        (show $ Set.size badStates) ++ " bad states, " ++
        (show $ Set.size goodStates) ++ " good states, " ++
        (show $ length usedFeatures) ++ " used features, " ++
        (show $ qSize queue) ++ " paths in queue."

      case qPeek queue of
        Nothing -> log_d $ "***** queue is empty"
        Just qh -> log_d $ "***** Head of queue: " ++ (show . length . qe_clauses $ qh) ++ " clauses plus: " ++ (show . aAnd . (map f_assertion) . qe_candidate $ qh)

      let context = SepCtx queue usedFeatures maxClauseSize
      (mSeparator, context') <- runStateT (findSeparator badStates goodStates) context

      let lctx' = LearnerContext (Just unusedFeatures) (Just usedFeatures) (Just $ ctx_queue context') badStates
      case mSeparator of
        Nothing -> pure (lctx', Nothing)
        Just separator -> pure (lctx', Just . aOr $ map clauseToAssertion separator)

addMissingNames :: forall t. (Ord t, Embeddable Integer t) => [Name] -> ProgState t -> ProgState t
addMissingNames names progState = foldr
                                  (\name st -> if Map.member name st
                                    then st
                                    else Map.insert name (embed 0) st)
                                  progState names

featureToEntry :: Ord t => Set (ProgState t) -> Set (ProgState t) -> Feature t -> DTLQueueEntry t
featureToEntry badStates goodStates feat@(Feature _ rejectedBads acceptedGoods) =
  DTLQueueEntry [] [feat] (Set.difference badStates rejectedBads) (Set.difference goodStates acceptedGoods)

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

prepareFeatures :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , Pretty t )
                => [ProgState t]
                -> [ProgState t]
                -> [Assertion t]
                -> Ceili ([Assertion t], [Feature t])
prepareFeatures _ _ [] = pure ([], [])
prepareFeatures badStates goodStates (a:as) = do
  (_, rejectedBads) <- splitStates a badStates
  (restUnused, restUsed) <- prepareFeatures badStates goodStates as
  if null rejectedBads
    then pure (a:restUnused, restUsed)
    else do
      (acceptedGoods, _) <- splitStates a goodStates
      if null acceptedGoods
        then pure (a:restUnused, restUsed)
        else
         let feature = Feature a (Set.fromList rejectedBads) (Set.fromList acceptedGoods)
         in pure (restUnused, feature:restUsed)

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
            -> DTLQueue t
            -> Ceili (DTLQueue t)
updateQueue oldBadStates newBadStates queue = do
  -- TODO: Cleanup duplication wrt updateFeatures
  let badsToAdd = Set.toList $ Set.difference newBadStates oldBadStates
  let rejects assertion state = do
        result <- testState assertion state
        pure $ if result then Nothing else Just state
  let updateFeature (Feature assertion oldRejectedBads oldAcceptedGoods) = do
        rejectionsToAdd <- sequence $ map (rejects assertion) badsToAdd
        let newRejectedBads = Set.union oldRejectedBads (Set.fromList $ catMaybes rejectionsToAdd)
        pure $ Feature assertion newRejectedBads oldAcceptedGoods
  let updateClause (Clause features oldRejectedBads oldAcceptedGoods) = do
        features' <- sequence $ map updateFeature features
        let newRejectedBads = Set.unions $ map f_rejectedBads features'
        if and $ map (flip Set.member $ newRejectedBads) badsToAdd
               then pure . Just $ Clause features' newRejectedBads oldAcceptedGoods
               else pure Nothing
  let updateEntry (DTLQueueEntry clauses candidate unrejectedBads unacceptedGoods) = do
        mClauses' <- sequence $ map updateClause clauses
        let clauses' = catMaybes mClauses'
        if length clauses' < length mClauses'
          then pure Nothing
          else do
            candidate' <- sequence $ map updateFeature candidate
            let rejectedBads' = Set.unions $ map f_rejectedBads candidate'
            pure . Just $ DTLQueueEntry clauses' candidate' (Set.difference newBadStates rejectedBads') unacceptedGoods

  let queueList = concat $ map Set.toList $ Map.elems queue
  mQueueList' <- sequence $ map updateEntry queueList
  let queue' = foldr qInsert Map.empty (catMaybes mQueueList')
  log_d $ "[DTLearn] Queue updated, removed " ++ (show $ qSize queue - qSize queue') ++ " item(s)."
  pure queue'

findSeparator :: ( Ord t
                 , StatePredicate (Assertion t) t
                 , Pretty t
                 )
              => Set (ProgState t)
              -> Set (ProgState t)
              -> SepM t (Maybe [Clause t])
findSeparator badStates goodStates = do
  mEntry <- dequeue
  case mEntry of
    Nothing    -> do
      -- Queue is empty, fail.
      lift . log_d $ "[DTLearn] Search queue is empty, giving up."
      pure Nothing
    Just entry -> case (qe_candidate entry) of
      [] -> do
        lift . log_d $ "******* Found empty candidate, reseeding."
        allFeatures <- getFeatures
        let toEntry feat@(Feature _ rejectedBads acceptedGoods) =
                DTLQueueEntry (qe_clauses entry) [feat] (Set.difference badStates rejectedBads) (Set.difference goodStates acceptedGoods)
        mapM_ enqueue $ map toEntry allFeatures
        findSeparator badStates goodStates
      _  -> if Set.null (qe_unacceptedGoods entry) && Set.null (qe_unrejectedBads entry)
            then do
                -- No more remaining good states to cover, succeed.
                clauses <- entryToClauses badStates goodStates entry
                lift . log_d $ "[DTLearn] Found separator: " ++ (show $ clausesToAssertion clauses)
                enqueue entry -- Re-enqueue in case we need to revisit after further counterexamples.
                pure $ Just clauses
            else enqueueNext badStates goodStates entry >> findSeparator badStates goodStates

entryToClauses :: ( Ord t
                  , StatePredicate (Assertion t) t)
               => Set (ProgState t)
               -> Set (ProgState t)
               -> DTLQueueEntry t
               -> SepM t [Clause t]
entryToClauses badStates goodStates (DTLQueueEntry clauses candidate _ _) = case candidate of
  [] -> pure clauses
  _  ->  do
    let candidateAssertion = aAnd $ map f_assertion candidate
    (_, rejectedBads)  <- lift $ splitStates candidateAssertion (Set.toList badStates)
    (acceptedGoods, _) <- lift $ splitStates candidateAssertion (Set.toList goodStates)
    let clause' = Clause candidate (Set.fromList rejectedBads) (Set.fromList acceptedGoods)
    pure $ clause':clauses

clausesToAssertion :: [Clause t] -> Assertion t
clausesToAssertion = aOr . concat . map (map f_assertion . c_features)

enqueueNext :: ( Ord t
               , StatePredicate (Assertion t) t
               , Pretty t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> DTLQueueEntry t
            -> SepM t ()
enqueueNext badStates goodStates entry@(DTLQueueEntry _ entryFeatures unrejectedBads unacceptedGoods) = do
  maxClauseSize <- getMaxClauseSize
  if length entryFeatures >= maxClauseSize
    then pure ()
    else do
      allFeatures <- getFeatures
      let useful feature = (not $ Set.disjoint (f_acceptedGoods feature) unacceptedGoods)
                        && (not $ Set.disjoint (f_rejectedBads  feature) unrejectedBads)
      let usefulFeatures = filter useful allFeatures
--      lift . log_d $ "[DTLearn] Considering " ++ (show $ length usefulFeatures) ++ " useful features."
      nextLevel <- nextEntries badStates goodStates entry usefulFeatures
      if length nextLevel > 0
        then lift . log_d $ "[DTLearn] Enqueueing " ++ (show $ length nextLevel) ++ " new search paths."
        else pure ()
--      lift . log_d $ "**** (head): " ++ (if null nextLevel then "<empty>" else show . aAnd . (map f_assertion) . qe_candidate . head $ nextLevel)
      mapM_ enqueue nextLevel


nextEntries :: ( Ord t
               , StatePredicate (Assertion t) t
               , Pretty t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> DTLQueueEntry t
            -> [Feature t]
            -> SepM t [DTLQueueEntry t]
nextEntries _ _ _ [] = pure []
nextEntries badStates goodStates entry@(DTLQueueEntry oldClauses oldCandidate oldUnrejectedBads oldUnacceptedGoods) (newFeature:rest) = do
  let newCandidate = newFeature:oldCandidate
  let newAssertion = aAnd $ map f_assertion newCandidate
  (newAcceptedGoodsList, _) <- lift $ splitStates newAssertion $ Set.toList goodStates
  let newAcceptedGoods = Set.fromList newAcceptedGoodsList
  let clauseAcceptedGoods = foldr Set.union Set.empty $ map c_acceptedGoods oldClauses
  if Set.isSubsetOf newAcceptedGoods clauseAcceptedGoods
    then nextEntries badStates goodStates entry rest -- The proposed clause isn't buying us anything.
    else do
      let newRejectedBads = Set.unions (map f_rejectedBads newCandidate)
      let newUnrejectedBads = Set.difference badStates newRejectedBads
      let newUnacceptedGoods = Set.difference goodStates $ Set.union newAcceptedGoods clauseAcceptedGoods
      if Set.null newUnrejectedBads
        then do
          newClauses <- entryToClauses badStates goodStates entry
          newEntries <- seedNewClause badStates goodStates newClauses
          pure . (newEntries ++) =<< nextEntries badStates goodStates entry rest
        else do
          let newEntry = DTLQueueEntry oldClauses newCandidate newUnrejectedBads newUnacceptedGoods
          pure . (newEntry:) =<< nextEntries badStates goodStates entry rest

seedNewClause :: Ord t => Set (ProgState t) -> Set (ProgState t) -> [Clause t] -> SepM t [DTLQueueEntry t]
seedNewClause badStates goodStates clauses = do
  allFeatures <- getFeatures
  let createEntry feature@(Feature _ rejectedBads acceptedGoods) =
        let
          unrejectedBads  = Set.difference badStates rejectedBads
          unacceptedGoods = Set.difference goodStates acceptedGoods
        in DTLQueueEntry clauses [feature] unrejectedBads unacceptedGoods
  pure $ map createEntry allFeatures


clauseToAssertion :: Clause t -> Assertion t
clauseToAssertion = aAnd . (map f_assertion) . c_features
