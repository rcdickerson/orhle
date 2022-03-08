{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Orhle.CInvGen
  ( Configuration(..)
  , Job(..)
  , cInvGen

  -- Exposed for testing:
  , CIEnv(..)
  , CiM
  , Clause(..)
  , Entry(..)
  , Feature(..)
  , Queue
  , RootClause(..)
  , UpdateFlag(..)
  , addNewlyUsefulCandidates
  , buildCurrentResult
  , closeNames
  , entryScore
  , getFeatures
  , getFeatureCandidates
  , getRemainingGoods
  , getRootClauses
  , getQueue
  , learnSeparator
  , mkCIEnv
  , qInsert
  , qPop
  , addRootClause
  , updateFeature
  , updateQueue
  , updateRootClauses
  , usefulFeatures
  ) where

import Debug.Trace

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import Ceili.PTS ( BackwardPT )
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Data.Either ( partitionEithers )
import Data.List ( partition )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Prettyprinter


-------------------
-- Configuration --
-------------------

data Configuration c p t = Configuration
  { cfgMaxFeatureSize   :: Int
  , cfgMaxClauseSize    :: Int
  , cfgFeatureGenerator :: Int -> Set (Assertion t)
  , cfgWpSemantics      :: BackwardPT c p t
  , cfgWpContext        :: c
  }


----------
-- Jobs --
----------

data Job p t = Job
  { jobBadStates  :: Set (ProgState t)
  , jobGoodStates :: Set (ProgState t)
  , jobLoopCond   :: Assertion t
  , jobLoopBody   :: p
  , jobPostCond   :: Assertion t
  }

----------------------
-- Type Constraints --
----------------------

type CIConstraints t = ( AssertionParseable t
                       , Embeddable Integer t
                       , Ord t
                       , Pretty t
                       , SMT.SatCheckable t
                       , SMT.ValidCheckable t
                       , StatePredicate (Assertion t) t
                       )

--------------
-- Features --
--------------

data Feature t = Feature
  { featAssertion     :: Assertion t
  , featRejectedBads  :: Set (ProgState t)
  , featAcceptedGoods :: Set (ProgState t)
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Feature t) where
  pretty (Feature assertion bads goods) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Assertion:" <+> pretty assertion
    , pretty "Rejected bads:" <+> align (prettyProgStates (Set.toList bads))
    , pretty "Accepted goods:" <+> align (prettyProgStates (Set.toList goods))
    ]


-------------
-- Clauses --
-------------

data Clause t = Clause
  { clauseFeatures      :: [Feature t]
  , clauseAcceptedGoods :: Set (ProgState t)
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Clause t) where
  pretty (Clause features accepted) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Features:" <+> pretty features
    , pretty "Clause accepts:" <+> pretty (Set.toList accepted)
    ]

emptyClause :: Clause t
emptyClause = Clause [] Set.empty

nullClause :: Clause t -> Bool
nullClause (Clause features _) = null features

clauseSize :: Clause t -> Int
clauseSize (Clause features _) = length features


------------------
-- Root Clauses --
------------------

data RootClause t = RootClause
  { rcClause :: (Clause t)
  , rcCovers :: [RootClause t]
  } deriving (Eq, Ord, Show)

rootClauseAcceptedGoods :: RootClause t -> Set (ProgState t)
rootClauseAcceptedGoods (RootClause clause _) = clauseAcceptedGoods clause

rootClauseAssertion :: RootClause t -> Assertion t
rootClauseAssertion (RootClause clause _) = aAnd . map featAssertion . clauseFeatures $ clause


------------------
-- Seach Queues --
------------------

type Queue t = Map Int (Set (Entry t))

data Entry t = Entry
  { entryCandidate     :: [Feature t]
  , entryRejectedBads  :: Set (ProgState t)
  , entryAcceptedGoods :: Set (ProgState t)
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Entry t) where
  pretty (Entry candidate rejected accepted) = align $
        pretty "Candidate["
    <>  pretty (Set.size accepted)
    <>  pretty "/"
    <>  pretty (Set.size rejected)
    <>  pretty "]:"
    <+> pretty candidate


nullEntry :: Entry t -> Bool
nullEntry = null . entryCandidate

qSize :: Queue t -> Int
qSize = Map.foldr (\set count -> count + Set.size set) 0

qInsert :: CIConstraints t => Entry t -> Queue t -> Queue t
qInsert entry queue =
  let score = entryScore entry
  in case Map.lookup score queue of
    Nothing  -> Map.insert score (Set.singleton entry) queue
    Just set -> Map.insert score (Set.insert entry set) queue

qPop :: Queue t -> (Maybe (Entry t), Queue t)
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


-------------------
-- Cost Function --
-------------------

entryScore :: CIConstraints t => Entry t -> Int
entryScore (Entry candidate rejected optimAccepted) =
  let
    numRejected   = Set.size rejected
    candidateSize = length candidate
    acceptedSize  = Set.size optimAccepted
  in (10 * acceptedSize) + numRejected - candidateSize


-----------------------
-- Computation Monad --
-----------------------

data CIEnv t = CIEnv { envQueue             :: Queue t
                     , envBadStates         :: Set (ProgState t)
                     , envGoodStates        :: Set (ProgState t)
                     , envRootClauses       :: [RootClause t]
                     , envFeatures          :: Set (Feature t)
                     , envFeatureCandidates :: [Assertion t]
                     , envGoalQuery         :: Assertion t -> Ceili (Assertion t)
                     , envStateNames        :: [Name]
                     , envMaxClauseSize     :: Int
                     }
type CiM t = StateT (CIEnv t) Ceili

mkCIEnv :: CIConstraints t => Configuration c p t -> Job p t -> CIEnv t
mkCIEnv config job =
  let
    nameList            = Set.unions . (map namesIn) . Set.toList
    names               = Set.toList $ Set.union (nameList . jobBadStates  $ job)
                                                 (nameList . jobGoodStates $ job)
    closedBads          = Set.map (closeNames names) (jobBadStates job)
    closedGoods         = Set.map (closeNames names) (jobGoodStates job)
    fCandidates         = Set.toList $ (cfgFeatureGenerator config) (cfgMaxFeatureSize config)
    loopCond            = jobLoopCond job
    negLoopCond         = Not $ loopCond
    maxClauseSize       = cfgMaxClauseSize config
    goalQuery candidate = do
      weakestPre <- (cfgWpSemantics config) (cfgWpContext config) (jobLoopBody job) candidate
      pure $ aAnd [ Imp (aAnd [candidate, negLoopCond]) (jobPostCond job) -- Establishes Post
                  , Imp (aAnd [candidate, loopCond]) weakestPre           -- Inductive
                  ]
  in CIEnv Map.empty closedBads closedGoods [] Set.empty fCandidates goalQuery names maxClauseSize

getQueue :: CiM t (Queue t)
getQueue = get >>= pure . envQueue

getBadStates :: CiM t (Set (ProgState t))
getBadStates = get >>= pure . envBadStates

getGoodStates :: CiM t (Set (ProgState t))
getGoodStates = get >>= pure . envGoodStates

getRootClauses :: CiM t [RootClause t]
getRootClauses = get >>= pure . envRootClauses

getFeatures :: CiM t (Set (Feature t))
getFeatures = get >>= pure . envFeatures

getFeatureCandidates :: CiM t [Assertion t]
getFeatureCandidates = get >>= pure . envFeatureCandidates

getMaxClauseSize :: CiM t Int
getMaxClauseSize = get >>= pure . envMaxClauseSize

putQueue :: Queue t -> CiM t ()
putQueue queue = do
  CIEnv _ bads goods roots features fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots features fCandidates goalQ names mcs

putBadStates :: Set (ProgState t) -> CiM t ()
putBadStates badStates = do
  CIEnv queue _ goods roots features fCandidates goalQ names mcs <- get
  put $ CIEnv queue badStates goods roots features fCandidates goalQ names mcs

putRootClauses :: [RootClause t] -> CiM t ()
putRootClauses roots = do
  CIEnv queue bads goods _ features fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots features fCandidates goalQ names mcs

putFeatures :: Set (Feature t) -> CiM t ()
putFeatures features = do
  CIEnv queue bads goods roots _ fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots features fCandidates goalQ names mcs

putFeatureCandidates :: [Assertion t] -> CiM t ()
putFeatureCandidates fCandidates = do
  CIEnv queue bads goods roots features _ goalQ names mcs <- get
  put $ CIEnv queue bads goods roots features fCandidates goalQ names mcs

addFeature :: Ord t => Feature t -> CiM t ()
addFeature feature = do
  CIEnv queue bads goods roots features fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots (Set.insert feature features) fCandidates goalQ names mcs

enqueue :: CIConstraints t => Entry t -> CiM t ()
enqueue entry = do
  queue <- getQueue
  putQueue $ qInsert entry queue

dequeue :: CiM t (Maybe (Entry t))
dequeue = do
  queue <- getQueue
  let (elt, queue') = qPop queue
  putQueue queue'
  pure elt

clog_d :: String -> CiM t ()
clog_d = lift . log_d

clog_e :: String -> CiM t ()
clog_e = lift . log_e


--------------------------------
-- CInvGen (Main Entry Point) --
--------------------------------

cInvGen :: CIConstraints t
        => Configuration c p t
        -> Job p t
        -> Ceili (Maybe (Assertion t))
cInvGen config job = do
  log_i $ "[CInvGen] Beginning invariant inference"
  let env = mkCIEnv config job
  log_d $ "[CInvGen] " ++ (show . length . envFeatureCandidates $ env) ++ " initial feature candidates."
  evalStateT cInvGen' env

cInvGen' :: CIConstraints t => CiM t (Maybe (Assertion t))
cInvGen' = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  clog_d $ "[CInvGen] Starting vPreGen pass"
  clog_d . show $ pretty "[CInvGen]   good states:" <+> pretty (Set.size goodStates)
  clog_d . show $ pretty "[CInvGen]   bad states: " <+> pretty (Set.size badStates)
  -- Try to learn a separator. If we find one, check to see if it meets the goal criteria.
  -- If it does, return it. Otherwise, add the new counterexample and recurse.
  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> clog_d "[CInvGen] Unable to find separator." >> pure Nothing
    Just separator -> do
      clog_d . show $ pretty "[CInvGen] Candidate precondition:" <+> (align . pretty) separator
      goalStatus <- checkGoal separator
      case goalStatus of
        GoalCex cex -> do
          clog_d . show $ pretty "[CInvGen] Found counterexample:" <+> (align . pretty) cex
          addBadState cex
          cInvGen'
        GoalMet -> do
          clog_d . show $ pretty "[CInvGen] Found invariant:" <+> (align . pretty) separator
          pure $ Just separator
        SMTError msg -> do
          clog_e . show $ pretty "[CInvGen]" <+> pretty msg
                      <+> pretty "on candidate" <+> (align . pretty) separator
          cInvGen' -- Continue now that the problematic assertion is out of the queue.

data GoalStatus t = GoalMet
                  | GoalCex (ProgState t)
                  | SMTError String

checkGoal :: CIConstraints t => Assertion t -> CiM t (GoalStatus t)
checkGoal candidate = do
  goalQuery <- get >>= pure . envGoalQuery
  mCex <- lift $ goalQuery candidate >>= findCounterexample
  case mCex of
    FormulaValid -> pure GoalMet
    Counterexample cex -> do
      let cexState = extractState cex
      pure $ GoalCex cexState
    SMTTimeout -> pure $ SMTError "SMT timeout"
    SMTUnknown -> pure $ SMTError "SMT returned unknown"


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: CIConstraints t => CiM t (Maybe (Assertion t))
learnSeparator = do
  queue      <- getQueue
  goodStates <- getGoodStates
  badStates  <- getBadStates
  clog_d $ "[CInvGen] Beginning separator search. Queue size: " ++ (show $ qSize queue)
  -- Short circuit on trivial separation cases.
  if Set.null badStates
    then do clog_d "[CInvGen] No bad states, returning true."; pure $ Just ATrue
  else if Set.null goodStates
    then do clog_d "[CInvGen] No good states, returning false."; pure $ Just AFalse
  else learnSeparator'

learnSeparator' :: CIConstraints t => CiM t (Maybe (Assertion t))
learnSeparator' = do
  remaining <- getRemainingGoods
  if Set.null remaining
    then pure . Just =<< buildCurrentResult
    else do
      mEntry <- dequeue
      case mEntry of
        Nothing -> do
          clog_d $ "[CInvGen] Search queue is empty, failing."
          pure Nothing
        Just entry -> do
          maxClauseSize <- getMaxClauseSize
          if length (entryCandidate entry) >= maxClauseSize
            then learnSeparator'
            else do
              nextFeatures <- usefulFeatures entry
              enqueueNextLevel entry nextFeatures
              learnSeparator'

usefulFeatures :: CIConstraints t => Entry t -> CiM t [Feature t]
usefulFeatures (Entry candidate enRejectedBads enAcceptedGoods) = do
  rootsAccepted <- getRootsAccepted
  if Set.isSubsetOf enAcceptedGoods rootsAccepted
    then pure [] -- Short circuit if there are no possible useful features.
    else do
      useful <- case candidate of
        [] ->
          -- The candidate is empty. A useful kickoff to a new clause candidate
          -- is any feature accepting currently unaccepted good states.
          pure $ \feature -> not $ Set.isSubsetOf (featAcceptedGoods feature) rootsAccepted
        _  -> do
          -- A useful addition to an existing candidate rejects something new
          -- while not bringing the accepted states for the new candidate
          -- down to either 1) the empty set or 2) a subset of of the good
          -- states already accepted by the entry's clauses. (Note the former
          -- condition is not a subcase of the latter since there may not
          -- be any non-trivial root clauses yet, and empty set is a subset
          -- of itself.)
          badStates <- getBadStates
          let enRemainingBads = Set.difference badStates enRejectedBads
          pure $ \feature ->
                   let optimisticAccepts = Set.intersection (featAcceptedGoods feature) enAcceptedGoods
                   in (not $ Set.disjoint (featRejectedBads feature) enRemainingBads)
                   && (not $ Set.null optimisticAccepts)
                   && (not $ Set.isSubsetOf optimisticAccepts rootsAccepted)
      getFeatures >>= pure . filter useful . Set.toList

enqueueNextLevel :: CIConstraints t => Entry t -> [Feature t] -> CiM t ()
enqueueNextLevel _ [] = pure ()
enqueueNextLevel entry@(Entry candidate enRejectedBads _) (newFeature:rest) = do
  let newCandidate = newFeature:candidate
  -- A useful feature *optimistically* accepted an interesting set of good
  -- states, but now we will do the SMT work to make sure.
  goodStates    <- getGoodStates
  rootsAccepted <- getRootsAccepted
  let newCandidateAssertion = aAnd $ map featAssertion newCandidate
  (newAcceptedGoodsList, _) <- lift $ splitStates newCandidateAssertion $ Set.toList goodStates
  let newAcceptedGoods = Set.fromList newAcceptedGoodsList
  if Set.isSubsetOf newAcceptedGoods rootsAccepted
    then
      -- It turns out the accepted good states are not intersting.
      enqueueNextLevel entry rest
    else do
      badStates <- getBadStates
      let newRejectedBads = Set.union enRejectedBads (featRejectedBads newFeature)
      if newRejectedBads == badStates
        then do
          -- We found a new root clause.
          addRootClause $ Clause newCandidate newAcceptedGoods
          remainingGoods <- getRemainingGoods
          if Set.null remainingGoods
            then pure ()
            else enqueueNextLevel entry rest
        else do
          enqueue $ Entry newCandidate newAcceptedGoods newRejectedBads
          enqueueNextLevel entry rest


------------------------
-- Root Clause Update --
------------------------

insertRootClause :: CIConstraints t => Clause t -> [RootClause t] -> [RootClause t]
insertRootClause newClause rootList =
  let
    checkCovers root     = (rcClause root) `isCoveredBy` newClause
    checkCoveredBy root  = newClause `isCoveredBy` (rcClause root)
    (covered, uncovered) = partition checkCovers rootList
    coveredBy            = filter checkCoveredBy rootList
  in case coveredBy of
    [] -> (RootClause newClause covered):uncovered
    (RootClause rClause rCovers):rest -> (RootClause rClause (insertRootClause newClause rCovers)):rest

addRootClause :: CIConstraints t => Clause t -> CiM t ()
addRootClause clause = getRootClauses >>= pure . insertRootClause clause >>= putRootClauses

isCoveredBy :: Ord t => Clause t -> Clause t -> Bool
isCoveredBy clause1 clause2 = Set.isSubsetOf (clauseAcceptedGoods clause1) (clauseAcceptedGoods clause2)


---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CIConstraints t => ProgState t -> CiM t ()
addBadState badState = do
  -- Note: we don't eagerly flush entries which no longer cover good states
  -- outside the root clause accepted goods. Instead, this check is done
  -- for all entries in learnSeparator / usefulFeatures.
  getBadStates   >>= pure . (Set.insert        badState) >>= putBadStates
  getFeatures    >>= lift . (updateFeatures    badState) >>= putFeatures
  getRootClauses >>= lift . (updateRootClauses badState) >>= putRootClauses
  getQueue       >>= lift . (updateQueue       badState) >>= putQueue
  addNewlyUsefulFeatures   badState
  addNewlyUsefulCandidates badState

addNewlyUsefulFeatures :: CIConstraints t => ProgState t -> CiM t ()
addNewlyUsefulFeatures newBadState = do
  features      <- getFeatures
  rootsAccepted <- getRootsAccepted
  let featuresList = Set.toList features
  let useful feature = (Set.member newBadState $ featRejectedBads feature)
                    && (not $ Set.isSubsetOf (featAcceptedGoods feature) rootsAccepted)
  let newlyUseful = filter useful featuresList
  mapM_ enqueue $ map featureToEntry newlyUseful

addNewlyUsefulCandidates :: CIConstraints t => ProgState t -> CiM t ()
addNewlyUsefulCandidates newBadState = do
  featureCandidates <- getFeatureCandidates
  let rejectsNewBad assertion = do
        result <- lift $ testState assertion newBadState
        pure $ if result then Left assertion else Right assertion
  (candidates', newlyUseful) <- pure . partitionEithers =<< mapM rejectsNewBad featureCandidates
  maybeUseful <- mapM assertionToFeature newlyUseful
  let newFeatures = filter (not . Set.null . featAcceptedGoods) maybeUseful

  -- Remember the new features so we don't have do duplicate the SMT work,
  -- but only actually enqueue the ones who accept new states.
  rootsAccepted <- getRootsAccepted
  let useful feature = not $ Set.isSubsetOf (featAcceptedGoods feature) rootsAccepted
  let featuresToEnqueue = filter useful newFeatures

  putFeatureCandidates candidates'
  mapM_ addFeature newFeatures
  mapM_ enqueue $ map featureToEntry featuresToEnqueue


-- Update Mechanics:

data UpdateFlag = Accepts
                | Rejects
                deriving (Ord, Eq, Show)

isRejects :: UpdateFlag -> Bool
isRejects = (== Rejects)

updateClause :: CIConstraints t => ProgState t -> Clause t -> Ceili (Clause t, UpdateFlag)
updateClause newBadState (Clause features acceptedGoods) = do
  (features', updateFlags) <- pure . unzip =<< mapM (updateFeature newBadState) features
  let flag = if any isRejects updateFlags then Rejects else Accepts
  pure (Clause features' acceptedGoods, flag)

-- updateRootClause :: CIConstraints t => ProgState t -> RootClause t -> Ceili [RootClause t]
-- updateRootClause newBadState (RootClause clause covers) = do
--   (clause', clauseFlag) <- updateClause newBadState clause
--   covers' <- updateRootClauses newBadState covers
--   case clauseFlag of
--     Accepts -> pure $ covers'                      -- The root clause is no longer good.
--     Rejects -> pure $ [RootClause clause' covers'] -- The root clause is still good.

updateRootClauses :: CIConstraints t => ProgState t -> [RootClause t] -> Ceili [RootClause t]
updateRootClauses newBadState rootClauses = do
  -- Collect and update all clauses, throw away now-bad clauses, and rebuild the tree.
  let collectClauses (RootClause clause covers) = clause:(concat . map collectClauses $ covers)
  let allClauses = concat . map collectClauses $ rootClauses
  updatedClauses <- pure
                  . map fst
                  . filter (isRejects . snd)
                  =<< mapM (updateClause newBadState) allClauses
  pure $ foldr insertRootClause [] updatedClauses

updateFeature :: CIConstraints t => ProgState t -> Feature t -> Ceili (Feature t, UpdateFlag)
updateFeature newBadState (Feature assertion rejectedBads acceptedGoods) = do
  acceptsNewBad <- testState assertion newBadState
  let (rejectedBads', flag) = if acceptsNewBad
                              then (rejectedBads, Accepts)
                              else (Set.insert newBadState rejectedBads, Rejects)
  pure (Feature assertion rejectedBads' acceptedGoods, flag)

updateFeatures :: CIConstraints t => ProgState t -> Set (Feature t) -> Ceili (Set (Feature t))
updateFeatures newBadState features = do
  features' <- mapM (updateFeature newBadState) $ Set.toList features
  pure . Set.fromList . (map fst) $ features'

updateEntry :: CIConstraints t => ProgState t -> Entry t -> Ceili (Entry t)
updateEntry newBadState (Entry candidate rejected accepted) = do
  (candidate', updateFlags) <- pure . unzip =<< mapM (updateFeature newBadState) candidate
  let rejected' = if any isRejects updateFlags
                  then Set.insert newBadState rejected
                  else rejected
  pure $ Entry candidate' rejected' accepted

updateQueue :: CIConstraints t => ProgState t -> Queue t -> Ceili (Queue t)
updateQueue newBadState queue = do
  let entries = Set.toList . Set.unions . Map.elems $ queue
  updatedEntries <- mapM (updateEntry newBadState) entries
  pure $ foldr qInsert Map.empty updatedEntries


-----------------------
-- Entry Conversions --
-----------------------

featureToEntry :: Feature t -> Entry t
featureToEntry feature = Entry [feature] (featRejectedBads feature) (featAcceptedGoods feature)

assertionToFeature :: CIConstraints t => Assertion t -> CiM t (Feature t)
assertionToFeature assertion = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  (_, rejectedBads)  <- lift $ splitStates assertion $ Set.toList badStates
  (acceptedGoods, _) <- lift $ splitStates assertion $ Set.toList goodStates
  pure $ Feature assertion (Set.fromList rejectedBads) (Set.fromList acceptedGoods)


-------------
-- Utility --
-------------

closeNames :: CIConstraints t => [Name] -> ProgState t -> ProgState t
closeNames names state =
  let
    ensureIn name st = if Map.member name st
                       then st
                       else Map.insert name (embed (0 :: Integer)) st
  in foldr ensureIn state names

getRootsAccepted :: CIConstraints t => CiM t (Set (ProgState t))
getRootsAccepted = do
  rootClauses <- getRootClauses
  pure $ Set.unions $ map rootClauseAcceptedGoods rootClauses

getRemainingGoods :: CIConstraints t => CiM t (Set (ProgState t))
getRemainingGoods = do
  goodStates <- getGoodStates
  getRootsAccepted >>= pure . Set.difference goodStates

buildCurrentResult :: CIConstraints t => CiM t (Assertion t)
buildCurrentResult = pure . aOr . (map rootClauseAssertion) =<< getRootClauses

splitStates :: CIConstraints t => Assertion t -> [ProgState t] -> Ceili ([ProgState t], [ProgState t])
splitStates assertion states = do
  let resultPairs state = do result <- testState assertion state; pure (state, result)
  evaluations <- sequence $ map resultPairs states
  let (accepted, rejected) = partition snd evaluations
  pure (map fst accepted, map fst rejected)

-- TODO: This is fragile.
-- TODO: Close names?
extractState :: Pretty t => Assertion t -> ProgState t
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
