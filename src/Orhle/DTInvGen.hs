{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.DTInvGen
  ( dtInvGen

  -- Exposed for testing.
  , Clause(..)
  , DtiEnv(..)
  , DtiM
  , DTLQueue
  , DTLQueueEntry(..)
  , Feature(..)
  , addBadState
  , qInsert
  , updateQueue
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.PTS ( BackwardPT )
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import qualified Data.List as List
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter
import System.Random ( randomRIO )


--------------
-- Features --
--------------
data Feature t = Feature { f_assertion     :: Assertion t
                         , f_rejectedBads  :: Set (ProgState t)
                         , f_acceptedGoods :: Set (ProgState t)
                         } deriving (Ord, Show)

instance Eq t => Eq (Feature t)
  where f1 == f2 = (f_assertion f1) == (f_assertion f2)


-------------
-- Clauses --
-------------
data Clause t = Clause { c_features      :: [Feature t]
                       , c_rejectedBads  :: Set (ProgState t)
                       , c_acceptedGoods :: Set (ProgState t)
                       } deriving (Eq, Ord, Show)

------------
-- Queues --
------------

type DTLQueue t = Map Int (Set (DTLQueueEntry t))
data DTLQueueEntry t = DTLQueueEntry { qe_clauses         :: [Clause t]
                                     , qe_candidate       :: [Feature t]
                                     , qe_unrejectedBads  :: Set (ProgState t)
                                     , qe_unacceptedGoods :: Set (ProgState t)
                                     } deriving (Eq, Ord, Show)

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

-- The cost function for queue entries.
entryScore :: DTLQueueEntry t -> Int
entryScore (DTLQueueEntry clauses features unrejectedBads unacceptedGoods) =
  if Set.null unrejectedBads && Set.null unacceptedGoods
  then fromIntegral (maxBound :: Int)
  else let
    unrejectedBadsScore  = -1 * Set.size unrejectedBads
    unacceptedGoodsScore = -100 * Set.size unacceptedGoods
    clauseSizeScore      = -10 * length clauses
    featuresSizeScore    = -1 * length features
  in unrejectedBadsScore + unacceptedGoodsScore + clauseSizeScore + featuresSizeScore


-----------------
-- Computation --
-----------------

data DtiEnv t = DtiEnv { env_goodStates        :: Set (ProgState t)
                       , env_badStates         :: Set (ProgState t)
                       , env_loopConds         :: [Assertion t]
                       , env_queue             :: DTLQueue t
                       , env_features          :: Set (Feature t)
                       , env_featureCandidates :: [Assertion t]
                       , env_maxClauseSize     :: Int
                       , env_allNames          :: [Name]
                       , env_wpTransform       :: Assertion t -> Ceili (Assertion t)
                       }

type DtiM t = StateT (DtiEnv t) Ceili

getGoodStates :: DtiM t (Set (ProgState t))
getGoodStates = pure . env_goodStates =<< get

getBadStates :: DtiM t (Set (ProgState t))
getBadStates = pure . env_badStates =<< get

putBadStates :: Set (ProgState t) -> DtiM t ()
putBadStates badStates = do
  DtiEnv goodStates _ loopConds queue features candidates maxClauseSize allNames wpt <- get
  put $ DtiEnv goodStates badStates loopConds queue features candidates maxClauseSize allNames wpt

getLoopConds :: DtiM t [Assertion t]
getLoopConds = return . env_loopConds =<< get

getQueue :: DtiM t (DTLQueue t)
getQueue = get >>= pure . env_queue

getQueueSize :: DtiM t Int
getQueueSize = getQueue >>= pure . qSize

getFeatures :: DtiM t (Set (Feature t))
getFeatures = get >>= pure . env_features

computeWP :: Assertion t -> DtiM t (Assertion t)
computeWP assertion = do
  wpTrans <- get >>= pure . env_wpTransform
  wp <- lift $ wpTrans assertion
  pure wp

putFeatures :: Set (Feature t) -> DtiM t ()
putFeatures features = do
  DtiEnv goodStates badStates loopConds queue _ candidates maxClauseSize allNames wpt <- get
  put $ DtiEnv goodStates badStates loopConds queue features candidates maxClauseSize allNames wpt

getFeatureCandidates :: DtiM t [Assertion t]
getFeatureCandidates = get >>= pure . env_featureCandidates

putFeatureCandidates :: [Assertion t] -> DtiM t ()
putFeatureCandidates candidates = do
  DtiEnv goodStates badStates loopConds queue features _ maxClauseSize allNames wpt <- get
  put $ DtiEnv goodStates badStates loopConds queue features candidates maxClauseSize allNames wpt

envMaxClauseSize :: DtiM t Int
envMaxClauseSize = get >>= pure . env_maxClauseSize

getAllNames :: DtiM t [Name]
getAllNames = get >>= pure . env_allNames

putQueue :: (DTLQueue t) -> DtiM t ()
putQueue queue = do
  DtiEnv goodStates badStates loopConds _ features candidates maxClauseSize allNames wpt <- get
  put $ DtiEnv goodStates badStates loopConds queue features candidates maxClauseSize allNames wpt

dequeue :: DtiM t (Maybe (DTLQueueEntry t))
dequeue = do
  queue <- getQueue
  let (elt, queue') = qPop queue
  putQueue queue'
  pure elt

enqueue :: Ord t => DTLQueueEntry t -> DtiM t ()
enqueue entry = do
  queue <- getQueue
  putQueue $ qInsert entry queue

plog_e :: String -> DtiM t ()
plog_e = lift . log_e

plog_i :: String -> DtiM t ()
plog_i = lift . log_i

plog_d :: String -> DtiM t ()
plog_d = lift . log_d


----------------
-- DTInvGen --
----------------

dtInvGen :: ( Embeddable Integer t
            , Ord t
            , Pretty t
            , SMT.ValidCheckable t
            , StatePredicate (Assertion t) t
            , AssertionParseable t
            , SatCheckable t)
         => c
         -> Int
         -> Int
         -> BackwardPT c p t
         -> [Assertion t]
         -> p
         -> Assertion t
         -> [ProgState t]
         -> (Int -> Set (Assertion t))
         -> Ceili (Maybe (Assertion t))
dtInvGen ctx maxFeatureSize maxClauseSize backwardPT loopConds body post fullGoodStatesList featureGen = do
  log_i $ "[DTInvGen] Beginning invariant inference"
  goodStatesList <- lift . lift $ randomSample 50 fullGoodStatesList
  -- Add missing names to good states. TODO: This might not be the best place for this.
  let names = Set.toList . Set.unions $ map namesIn goodStatesList
  let goodStates = Set.fromList $ map (addMissingNames names) goodStatesList
  -------
  let rawFeatures = Set.toList $ featureGen maxFeatureSize
  log_d $ "[DTInvGen] " ++ (show $ length rawFeatures) ++ " initial features."
  let nLoopConds = map Not loopConds
  let goalQuery assertion = do
        wp <- computeWP assertion
        pure $ aAnd [ Imp (aAnd $ assertion:nLoopConds) post
                    , Not $ Imp (aAnd $ assertion:nLoopConds) AFalse
                    , Imp (aAnd $ assertion:loopConds) wp
                    ]
  let wpTransform = backwardPT ctx body
  evalStateT (vPreGen goalQuery) $ DtiEnv goodStates Set.empty loopConds Map.empty Set.empty rawFeatures maxClauseSize names wpTransform

-- Adapted from https://www.programming-idioms.org/idiom/158/random-sublist/2123/haskell
randomSample :: Int -> [a] -> IO [a]
randomSample k x | k >= length x = pure x
randomSample 0 x = pure []
randomSample k x = do
   i <- randomRIO (0, length x - 1)
   let (a, e:b) = splitAt i x
   l <- randomSample (k-1) (a ++ b)
   pure (e : l)

addMissingNames :: (Ord t, Embeddable Integer t) => [Name] -> ProgState t -> ProgState t
addMissingNames names progState = foldr
                                  (\name st -> if Map.member name st
                                    then st
                                    else Map.insert name (embed 0) st)
                                  progState names

envAddMissingNames :: (Ord t, Embeddable Integer t) => ProgState t -> DtiM t (ProgState t)
envAddMissingNames state = do
  names <- getAllNames
  pure $ addMissingNames names state


-------------
-- vPreGen --
-------------

vPreGen :: ( Embeddable Integer t
           , Ord t
           , Pretty t
           , SMT.ValidCheckable t
           , StatePredicate (Assertion t) t
           , AssertionParseable t
           , SatCheckable t)
        => (Assertion t -> DtiM t (Assertion t))
        -> DtiM t (Maybe (Assertion t))
vPreGen goalQuery = do
  goodStates <- getGoodStates
  badStates <- getBadStates
  plog_d $ "[DTInvGen] Starting vPreGen pass"
--  plog_d . show $ pretty "[DTInvGen] goal: " <+> pretty goal
  plog_d . show $ pretty "[DTInvGen]   good states: " <+> pretty (Set.size goodStates)
  plog_d . show $ pretty "[DTInvGen]   bad states: "  <+> pretty (Set.size badStates)
  mCandidate <- learnSeparator
  case mCandidate of
    Nothing -> do
      plog_d $ "[DTInvGen] vPreGen unable to find separator."
      return Nothing
    Just candidate -> do
      plog_d $ "[DTInvGen] vPreGen candidate precondition: " ++ (show . pretty) candidate
      query <- goalQuery candidate
      mCounter <- lift $ findCounterexample query
      case mCounter of
        Nothing -> do
          plog_d $ "[DTInvGen] vPreGen found satisfactory precondition: " ++ show candidate
          return $ Just candidate
        Just counter -> do
          plog_d $ "[DTInvGen] vPreGen found counterexample: " ++ show counter
          cexState <- envAddMissingNames $ extractState counter
          addBadState cexState >> vPreGen goalQuery

-- TODO: This is fragile.
extractState :: Pretty t => (Assertion t) -> (ProgState t)
extractState assertion = case assertion of
  Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> Map.unions $ map extractState as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: ( Embeddable Integer t
                  , Ord t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  , SatCheckable t
                  , ValidCheckable t
                  )
               => DtiM t (Maybe (Assertion t))
learnSeparator = do
  goodStates <- getGoodStates
  badStates <- getBadStates

  if Set.null goodStates || Set.null badStates
    then pure . Just $ ATrue
    else do
    queue <- getQueue
    plog_d $ "[DTInvGen] Beginning separator search. " ++
      (show $ Set.size badStates) ++ " bad states, " ++
      (show $ Set.size goodStates) ++ " good states, " ++
      (show $ qSize queue) ++ " paths in queue."
    case qPeek queue of
      Nothing -> plog_d $ "***** queue is empty"
      Just qh -> plog_d $ "***** Head of queue: " ++ (show . length . qe_clauses $ qh) ++
        " clauses plus: " ++ (show . aAnd . (map f_assertion) . qe_candidate $ qh) ++
        ", " ++ (show . Set.size . qe_unrejectedBads $ qh) ++ " unrejected features."

    mSeparator <- findSeparator badStates goodStates
    case mSeparator of
      Nothing -> pure Nothing
      Just separator -> pure . Just $ clausesToAssertion separator

findSeparator :: ( Ord t
                 , StatePredicate (Assertion t) t
                 , Pretty t
                 , ValidCheckable t
                 )
              => Set (ProgState t)
              -> Set (ProgState t)
              -> DtiM t (Maybe [Clause t])
findSeparator badStates goodStates = do
  mEntry <- dequeue
  case mEntry of
    Nothing -> do
      lift . log_d $ "[DTInvGen] Search queue is empty, giving up."
      pure Nothing
    Just entry ->
      if Set.null (qe_unacceptedGoods entry)
      then do
        -- Entry accepts all good states, succeed.
        let clauses = qe_clauses entry
        lift . log_d $ "[DTInvGen] Found separator: " ++ (show $ clausesToAssertion clauses)
        pure $ Just clauses
      else enqueueNext badStates goodStates entry >> findSeparator badStates goodStates

enqueueNext :: ( Ord t
               , StatePredicate (Assertion t) t
               , Pretty t
               , ValidCheckable t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> DTLQueueEntry t
            -> DtiM t ()
enqueueNext badStates goodStates entry@(DTLQueueEntry _ entryFeatures unrejectedBads unacceptedGoods) = do
  maxClauseSize <- envMaxClauseSize
  if length entryFeatures >= maxClauseSize
    then pure ()
    else do
      allFeatures <- getFeatures
      let useful feature = (not $ Set.disjoint (f_rejectedBads feature)  unrejectedBads)
                        && (not $ Set.disjoint (f_acceptedGoods feature) unacceptedGoods)
      let usefulFeatures = Set.filter useful allFeatures
--      lift . log_d $ "[DTInvGen] Considering " ++ (show $ length usefulFeatures) ++ " useful features."
      nextLevel <- nextEntries badStates goodStates entry $ Set.toList usefulFeatures
      -- if length nextLevel > 0
      --   then lift . log_d $ "[DTInvGen] Enqueueing " ++ (show $ length nextLevel) ++ " new search paths."
      --   else pure ()
--      lift . log_d $ "**** (head): " ++ (if null nextLevel then "<empty>" else show . aAnd . (map f_assertion) . qe_candidate . head $ nextLevel)
      mapM_ enqueue nextLevel


nextEntries :: ( Ord t
               , StatePredicate (Assertion t) t
               , Pretty t
               , ValidCheckable t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> DTLQueueEntry t
            -> [Feature t]
            -> DtiM t [DTLQueueEntry t]
nextEntries _ _ _ [] = pure []
nextEntries badStates goodStates entry@(DTLQueueEntry oldClauses oldCandidate _ oldUnacceptedGoods) (newFeature:rest) = do
  let newCandidate = newFeature:oldCandidate
  let newRejectedBads = Set.unions (map f_rejectedBads newCandidate)
  let newUnrejectedBads = Set.difference badStates newRejectedBads
  if Set.null newUnrejectedBads
    then do
      --isInductive <- checkInductive . aAnd . (map f_assertion) $ newCandidate
--      if not isInductive then
--        nextEntries badStates goodStates entry rest
--      else do
        let newAcceptedGoods = Set.unions $ map f_acceptedGoods newCandidate
        let newClause = Clause newCandidate newRejectedBads newAcceptedGoods
        let newClauses = newClause : oldClauses
        let newUnacceptedGoods = Set.difference goodStates newAcceptedGoods
        let newEntry = DTLQueueEntry newClauses [] badStates newUnacceptedGoods
        pure . (newEntry:) =<< nextEntries badStates goodStates entry rest
    else do
      let newEntry = DTLQueueEntry oldClauses newCandidate newUnrejectedBads oldUnacceptedGoods
      pure . (newEntry:) =<< nextEntries badStates goodStates entry rest

-- checkInductive :: ( ValidCheckable t
--                   , Pretty t
--                   ) => Assertion t -> DtiM t Bool
-- checkInductive assertion = do
--   conds <- getLoopConds
--   wp <- computeWP assertion
--   let query = Imp (And $ assertion:conds) wp
--   response <- lift . checkValid $ query
--   case response of
--     SMT.Valid        -> return True
--     SMT.Invalid _    -> return False
--     SMT.ValidUnknown -> do
--       plog_e $ "[DTInvGen] SMT solver returned unknown when checking inductivity. "
--                ++ "Treating candidate as non-inductive. Inductivity SMT query: "
--                ++ show query
--       return False

clauseToAssertion :: Clause t -> Assertion t
clauseToAssertion = aAnd . (map f_assertion) . c_features

clausesToAssertion :: [Clause t] -> Assertion t
clausesToAssertion = aOr . (map clauseToAssertion)


---------------------------
-- Counterexample Update --
---------------------------

addBadState :: ( Ord t
               , StatePredicate (Assertion t) t
               , Pretty t
               , ValidCheckable t
               )
            => ProgState t -> DtiM t ()
addBadState newBadState = do
  oldBadStates     <- getBadStates
  goodStates       <- getGoodStates
  candidates       <- getFeatureCandidates
  -- Update bad states set.
  let newBadStates = Set.insert newBadState oldBadStates
  putBadStates newBadStates
  -- Update features cache / feature candidates.
  updatedFeatures <- updateFeatures (Set.singleton newBadState) =<< getFeatures
  (candidates', newlyUsedFeatures) <- prepareFeatures (Set.toList newBadStates) (Set.toList goodStates) candidates
  putFeatures $ Set.union updatedFeatures $ Set.fromList newlyUsedFeatures
  putFeatureCandidates candidates'
  -- Update queue.
  newEntries <- sequence $ map (featureToEntry newBadStates goodStates) newlyUsedFeatures
  updatedQueue <- updateQueue oldBadStates (Set.singleton newBadState) =<< getQueue
  putQueue $ foldr qInsert updatedQueue newEntries

featureToEntry :: ( Ord t
                  , ValidCheckable t
                  , Pretty t
                  )
               => Set (ProgState t)
               -> Set (ProgState t)
               -> Feature t
               -> DtiM t (DTLQueueEntry t)
featureToEntry badStates goodStates feat@(Feature _ rejectedBads acceptedGoods) = do
  let unrejectedBads  = Set.difference badStates  rejectedBads
  let unacceptedGoods = Set.difference goodStates acceptedGoods
  if Set.null unrejectedBads
    then pure $ DTLQueueEntry [Clause [feat] rejectedBads acceptedGoods] [] badStates unacceptedGoods
--      isInductive <- checkInductive assertion
--      if isInductive
--        then pure $ DTLQueueEntry [Clause [feat] rejectedBads acceptedGoods] [] badStates (Set.difference goodStates acceptedGoods)
--        else pure $ DTLQueueEntry [] [feat] unrejectedBads goodStates
    else pure $ DTLQueueEntry [] [feat] unrejectedBads unacceptedGoods

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
                -> DtiM t ([Assertion t], [Feature t])
prepareFeatures _ _ [] = pure ([], [])
prepareFeatures badStates goodStates (a:as) = do
  (_, rejectedBads) <- lift $ splitStates a badStates
  (restUnused, restUsed) <- prepareFeatures badStates goodStates as
  if null rejectedBads
    then pure (a:restUnused, restUsed)
    else do
      (acceptedGoods, _) <- lift $ splitStates a goodStates
      let feature = Feature a (Set.fromList rejectedBads) (Set.fromList acceptedGoods)
      pure (restUnused, feature:restUsed)

updateFeatures :: ( Ord t
                  , StatePredicate (Assertion t) t
                  )
               => Set (ProgState t)
               -> Set (Feature t)
               -> DtiM t (Set (Feature t))
updateFeatures newBadStates features = do
  let newBadStatesList = Set.toList newBadStates
  let rejects assertion state = do
        result <- testState assertion state
        pure $ if result then Nothing else Just state
  let updateFeature (Feature assertion rejectedBads acceptedGoods) = do
        mBads <- sequence $ map (rejects assertion) newBadStatesList
        let newBads = Set.union rejectedBads (Set.fromList $ catMaybes mBads)
        pure $ Feature assertion newBads acceptedGoods
  features' <- lift . sequence . (map updateFeature) $ Set.toList features
  pure $ Set.fromList features'

updateQueue :: ( Ord t
               , StatePredicate (Assertion t) t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> DTLQueue t
            -> DtiM t (DTLQueue t)
updateQueue oldBadStates addedBadStates queue = do
  -- TODO: Cleanup duplication wrt updateFeatures
  let addedBadStatesList = Set.toList addedBadStates
  let rejects assertion state = do
        result <- testState assertion state
        pure $ if result then Nothing else Just state
  let updateFeature (Feature assertion oldRejectedBads oldAcceptedGoods) = do
        rejectionsToAdd <- sequence $ map (rejects assertion) addedBadStatesList
        let newRejectedBads = Set.union oldRejectedBads (Set.fromList $ catMaybes rejectionsToAdd)
        pure $ Feature assertion newRejectedBads oldAcceptedGoods
  let updateClause (Clause features _ oldAcceptedGoods) = do
        features' <- sequence $ map updateFeature features
        let newRejectedBads = Set.unions $ map f_rejectedBads features'
        if and $ map (flip Set.member $ newRejectedBads) addedBadStatesList
               then pure . Just $ Clause features' newRejectedBads oldAcceptedGoods
               else pure Nothing
  let updateEntry (DTLQueueEntry clauses candidate _ oldUnacceptedGoods) = do
        mClauses' <- sequence $ map updateClause clauses
        let clauses' = catMaybes mClauses'
        if length clauses' < length mClauses'
          then pure Nothing
          else do
            candidate' <- sequence $ map updateFeature candidate
            let rejected'       = Set.unions $ map f_rejectedBads candidate'
            let unrejectedBads' = Set.difference (Set.union oldBadStates addedBadStates) rejected'
            pure . Just $ DTLQueueEntry clauses' candidate' unrejectedBads' oldUnacceptedGoods

  let queueList = concat $ map Set.toList $ Map.elems queue
  mQueueList' <- lift . sequence . (map updateEntry) $ queueList
  let queue' = foldr qInsert Map.empty (catMaybes mQueueList')
  plog_d $ "[DTInvGen] Queue updated, removed " ++ (show $ qSize queue - qSize queue') ++ " item(s)."
  pure queue'
