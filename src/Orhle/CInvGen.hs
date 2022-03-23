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
  , FeatureCache(..)
  , Queue
  , RootClause(..)
  , UpdateFlag(..)
  , addNewlyUsefulCandidates
  , buildCurrentResult
  , closeNames
  , entryScore
  , fcAddFeature
  , fcEmpty
  , getFeatures
  , getFeatureCandidates
  , getRemainingGoods
  , getRootClauses
  , getQueue
  , learnSeparator
  , mkCIEnv
  , putRootClauses
  , qInsert
  , qPop
  , tagFeature
  , addRootClause
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
import Data.List ( partition, sort )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Prettyprinter


--------------------
-- Configurations --
--------------------

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
  , featAcceptedGoods :: Set (ProgState t)
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Feature t) where
  pretty (Feature assertion goods) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Assertion:" <+> pretty assertion
    , pretty "Accepted goods:" <+> align (prettyProgStates (Set.toList goods))
    ]


-------------------
-- Feature Cache --
-------------------

data FeatureCache t = FeatureCache
  { fcAllFeatures        :: Set (Feature t)
  , fcRejectedByFeature  :: Map (Feature t) (Set (ProgState t))
  , fcFeaturesByAccepted :: Map (ProgState t) (Set (Feature t))
  , fcFeaturesByRejected :: Map (ProgState t) (Set (Feature t))
  }

fcEmpty :: FeatureCache t
fcEmpty = FeatureCache Set.empty Map.empty Map.empty Map.empty

fcAddFeature :: Ord t => Feature t -> Set (ProgState t) -> FeatureCache t -> FeatureCache t
fcAddFeature feature rejected (FeatureCache features rejectedByFeature featsByAccepted featsByRejected) =
  let
    features' = Set.insert feature features
    rejectedByFeature' = Map.insert feature rejected rejectedByFeature
    featInsert st stMap = case Map.lookup st stMap of
                           Nothing  -> Map.insert st (Set.singleton feature) stMap
                           Just set -> Map.insert st (Set.insert feature set) stMap
    featsByAccepted' = foldr featInsert featsByAccepted $ Set.toList (featAcceptedGoods feature)
    featsByRejected' = foldr featInsert featsByRejected $ Set.toList rejected
  in FeatureCache features' rejectedByFeature' featsByAccepted' featsByRejected'

fcFeaturesWhichAccept :: Ord t => [ProgState t] -> FeatureCache t -> [Set (Feature t)]
fcFeaturesWhichAccept states cache =
  case states of
    [] -> []
    (s:ss) -> case Map.lookup s (fcFeaturesByAccepted cache) of
      Nothing -> fcFeaturesWhichAccept ss cache
      Just features -> features:(fcFeaturesWhichAccept ss cache)

fcFeaturesWhichReject :: Ord t => [ProgState t] -> FeatureCache t -> [Set (Feature t)]
fcFeaturesWhichReject states cache =
  case states of
    [] -> []
    (s:ss) -> case Map.lookup s (fcFeaturesByRejected cache) of
      Nothing -> fcFeaturesWhichAccept ss cache
      Just features -> features:(fcFeaturesWhichReject ss cache)


fcRejectedBads :: Ord t => Feature t -> FeatureCache t -> Set (ProgState t)
fcRejectedBads feature cache =
  case Map.lookup feature (fcRejectedByFeature cache) of
    Nothing       -> Set.empty
    Just rejected -> rejected


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


------------------
-- Root Clauses --
------------------

data RootClause t = RootClause
  { rcClause :: (Clause t)
  , rcCovers :: [RootClause t]
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (RootClause t) where
  pretty (RootClause clause covers) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Root Clause:" <+> pretty clause
    , pretty "Covers:" <+> pretty covers
    ]

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
  } deriving (Ord, Show)

-- TODO: Is this actually a good idea?
instance Ord t => Eq (Entry t) where
  entry1 == entry2 =
    Set.fromList (entryCandidate entry1) == Set.fromList (entryCandidate entry2)

instance Pretty t => Pretty (Entry t) where
  pretty (Entry candidate rejected accepted) = align $
        pretty "Candidate["
    <>  pretty (Set.size accepted)
    <>  pretty "/"
    <>  pretty (Set.size rejected)
    <>  pretty "]:"
    <+> pretty candidate

qSize :: Queue t -> Int
qSize = Map.foldr (\set count -> count + Set.size set) 0

qInsert :: CIConstraints t => Entry t -> Queue t -> Queue t
qInsert entry queue =
  let score = entryScore entry
  in case Map.lookup score queue of
    Nothing  -> Map.insert score (Set.singleton entry) queue
    Just set ->
      -- TODO: If the exact candidate feature set is already here, ignore?
      Map.insert score (Set.insert entry set) queue

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
                     , envRootsAccepted     :: Set (ProgState t)
                     , envFeatureCache      :: FeatureCache t
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
  in CIEnv Map.empty closedBads closedGoods [] Set.empty fcEmpty fCandidates goalQuery names maxClauseSize

getQueue :: CiM t (Queue t)
getQueue = get >>= pure . envQueue

getBadStates :: CiM t (Set (ProgState t))
getBadStates = get >>= pure . envBadStates

getGoodStates :: CiM t (Set (ProgState t))
getGoodStates = get >>= pure . envGoodStates

getRootClauses :: CiM t [RootClause t]
getRootClauses = get >>= pure . envRootClauses

getRootsAccepted :: CiM t (Set (ProgState t))
getRootsAccepted = get >>= pure . envRootsAccepted

getFeatureCache :: CiM t (FeatureCache t)
getFeatureCache = get >>= pure . envFeatureCache

getFeatures :: CiM t (Set (Feature t))
getFeatures = get >>= pure . fcAllFeatures . envFeatureCache

getFeatureRejectedBads :: Ord t => Feature t -> CiM t (Set (ProgState t))
getFeatureRejectedBads feature = do
  cache <- getFeatureCache
  pure $ fcRejectedBads feature cache

getFeaturesWhichAccept :: Ord t => [ProgState t] -> CiM t [Set (Feature t)]
getFeaturesWhichAccept states = do
  cache <- getFeatureCache
  pure $ fcFeaturesWhichAccept states cache

getFeaturesWhichReject :: Ord t => [ProgState t] -> CiM t [Set (Feature t)]
getFeaturesWhichReject states = do
  cache <- getFeatureCache
  pure $ fcFeaturesWhichReject states cache

getFeatureCandidates :: CiM t [Assertion t]
getFeatureCandidates = get >>= pure . envFeatureCandidates

getMaxClauseSize :: CiM t Int
getMaxClauseSize = get >>= pure . envMaxClauseSize

getStateNames :: CiM t [Name]
getStateNames = get >>= pure . envStateNames

putQueue :: Queue t -> CiM t ()
putQueue queue = do
  CIEnv _ bads goods roots rootsAccepted features fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots rootsAccepted features fCandidates goalQ names mcs

putBadStates :: Set (ProgState t) -> CiM t ()
putBadStates badStates = do
  CIEnv queue _ goods roots rootsAccepted features fCandidates goalQ names mcs <- get
  put $ CIEnv queue badStates goods roots rootsAccepted features fCandidates goalQ names mcs

putRootClauses :: Ord t => [RootClause t] -> CiM t ()
putRootClauses roots = do
  CIEnv queue bads goods _ _ features fCandidates goalQ names mcs <- get
  let accepted = Set.unions $ map rootClauseAcceptedGoods roots
  put $ CIEnv queue bads goods roots accepted features fCandidates goalQ names mcs

putFeatureCache :: FeatureCache t -> CiM t ()
putFeatureCache featureCache = do
  CIEnv queue bads goods roots rootsAccepted _ fCandidates goalQ names mcs <- get
  put $ CIEnv queue bads goods roots rootsAccepted featureCache fCandidates goalQ names mcs

putFeatureCandidates :: [Assertion t] -> CiM t ()
putFeatureCandidates fCandidates = do
  CIEnv queue bads goods roots rootsAccepted features _ goalQ names mcs <- get
  put $ CIEnv queue bads goods roots rootsAccepted features fCandidates goalQ names mcs

addFeature :: Ord t => Feature t -> Set (ProgState t) -> CiM t ()
addFeature feature rejected = do
  CIEnv queue bads goods roots rootsAccepted featureCache fCandidates goalQ names mcs <- get
  let featureCache' = fcAddFeature feature rejected featureCache
  put $ CIEnv queue bads goods roots rootsAccepted featureCache' fCandidates goalQ names mcs

enqueue :: CIConstraints t => Entry t -> CiM t ()
enqueue entry = do
  queue <- getQueue
  -- _ <- if (qSize queue `mod` 1000 == 1)
  --   then traceM $ "Queue size: " ++ (show $ qSize queue - 1)
  --   else pure ()
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
          putQueue $ Map.empty
          addBadState cex
          cInvGen'
        GoalMet -> do
          clog_d . show $ pretty "[CInvGen] Found invariant:" <+> (align . pretty) separator
          pure $ Just separator
        SMTError msg -> do
          clog_e . show $ pretty "[CInvGen]" <+> pretty msg
                      <+> pretty "on candidate" <+> (align . pretty) separator
          throwError "SMT error"
          --cInvGen' -- Continue now that the problematic assertion is out of the queue.

data GoalStatus t = GoalMet
                  | GoalCex (ProgState t)
                  | SMTError String

checkGoal :: CIConstraints t => Assertion t -> CiM t (GoalStatus t)
checkGoal candidate = do
  goalQuery <- get >>= pure . envGoalQuery
--  cquery <- lift (goalQuery candidate)
--  clog_d . show . align $ pretty "Goal query:" <+> pretty cquery
  mCex <- lift $ goalQuery candidate >>= findCounterexample
  case mCex of
    FormulaValid -> pure GoalMet
    Counterexample cex -> do
      cexState <- extractState cex
      pure $ GoalCex cexState
    SMTTimeout -> pure $ SMTError "SMT timeout"
    SMTUnknown -> pure $ SMTError "SMT returned unknown"


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: CIConstraints t => CiM t (Maybe (Assertion t))
learnSeparator = do
  queue      <- getQueue
  roots      <- getRootClauses
  goodStates <- getGoodStates
  badStates  <- getBadStates
  clog_d $ "[CInvGen] Beginning separator search."
  clog_d $ "[CInvGen]   Queue size: " ++ (show $ qSize queue)
  clog_d $ "[CInvGen]   Root size: "  ++ (show $ length roots)
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
              queue <- getQueue
              clog_d $ "[CInvGen] Useful features: " ++ (show $ length nextFeatures) ++ ", queue size: " ++ (show $ qSize queue)
              enqueueNextLevel entry nextFeatures
              learnSeparator'

usefulFeatures :: CIConstraints t => Entry t -> CiM t [Feature t]
usefulFeatures (Entry candidate enRejectedBads enAcceptedGoods) = do
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  if any (enAcceptedGoods `Set.isProperSubsetOf`) $ rootClauseAccepts
    then pure [] -- Short circuit if there are no possible useful features.
    else do
    case candidate of
      [] -> do
        -- The candidate is empty. A useful kickoff to a new clause candidate
        -- is any feature accepting currently unaccepted good states.
        pure . Set.toList . Set.unions =<< getFeaturesWhichAccept . Set.toList =<< getRemainingGoods
      _ ->  do
        -- A useful addition to an existing candidate rejects something new
        -- while not bringing the accepted states for the new candidate
        -- down to a subset of of the good states already accepted by the
        -- entry's clauses.
        let rootAcceptSet = Set.unions rootClauseAccepts
        acceptsSomethingGood <- case Set.null rootAcceptSet of
          True  -> pure . Set.unions =<< getFeaturesWhichAccept (Set.toList enAcceptedGoods)
          False -> do
            goodStates <- getGoodStates
            outsideRoot <- pure $ Set.difference goodStates rootAcceptSet
            acceptsOutsideRoot <- pure . Set.unions =<< getFeaturesWhichAccept (Set.toList outsideRoot)
            acceptsInsideEntry <- pure . Set.unions =<< getFeaturesWhichAccept (Set.toList enAcceptedGoods)
            pure $ Set.intersection acceptsOutsideRoot acceptsInsideEntry
        rejectsSomethingBad <- do
          badStates <- getBadStates
          let remainingBads = Set.difference badStates enRejectedBads
          pure . Set.unions =<< getFeaturesWhichReject (Set.toList remainingBads)
        pure . Set.toList $ Set.intersection rejectsSomethingBad acceptsSomethingGood

enqueueNextLevel :: CIConstraints t => Entry t -> [Feature t] -> CiM t ()
enqueueNextLevel _ [] = pure ()
enqueueNextLevel entry@(Entry candidate enRejectedBads _) (newFeature:rest) = do
  let newCandidate = newFeature:candidate
  -- A useful feature *optimistically* accepted an interesting set of good
  -- states, but now we will do the SMT work to make sure.
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  let newCandidateAssertion = aAnd $ map featAssertion newCandidate

  goodStates <- getGoodStates
  (newAcceptedGoodsList, _) <- lift $ splitStates newCandidateAssertion $ Set.toList goodStates
  let newAcceptedGoods = Set.fromList newAcceptedGoodsList

  if (any (newAcceptedGoods `Set.isProperSubsetOf`) rootClauseAccepts)
    then
      -- It turns out the accepted good states are not intersting.
      enqueueNextLevel entry rest
    else do
      badStates <- getBadStates
      newRejectedBads <- pure . Set.union enRejectedBads =<< getFeatureRejectedBads newFeature
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
    checkCovers root       = (rcClause root) `isCoveredBy` newClause
    checkCoveredBy root    = newClause `isCoveredBy` (rcClause root)
    (covered, uncovered)   = partition checkCovers rootList
    coveredBy              = filter checkCoveredBy rootList
    alreadyContained       = any (\rc -> newClause == rcClause rc) rootList

    checkDuplicate rclause = Set.fromList (clauseFeatures newClause) == Set.fromList (clauseFeatures rclause)
    duplicates             = any (checkDuplicate . rcClause) rootList
  in
    if alreadyContained || duplicates
    then rootList
    else case coveredBy of
      [] -> (RootClause newClause covered):uncovered
      (RootClause rClause rCovers):rest -> (RootClause rClause (insertRootClause newClause rCovers)):rest

addRootClause :: CIConstraints t => Clause t -> CiM t ()
addRootClause clause = getRootClauses >>= pure . insertRootClause clause >>= putRootClauses

isCoveredBy :: Ord t => Clause t -> Clause t -> Bool
isCoveredBy clause1 clause2 = Set.isProperSubsetOf (clauseAcceptedGoods clause1) (clauseAcceptedGoods clause2)


---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CIConstraints t => ProgState t -> CiM t ()
addBadState badState = do
  -- Note: we don't eagerly flush entries which no longer cover good states
  -- outside the root clause accepted goods. Instead, this check is done
  -- for all entries in learnSeparator / usefulFeatures.
  getBadStates    >>= pure . (Set.insert badState) >>= putBadStates
  getFeatureCache >>= updateFeatureCache badState  >>= putFeatureCache
  getRootClauses  >>= updateRootClauses  badState  >>= putRootClauses
  getQueue        >>= updateQueue        badState  >>= putQueue
  addNewlyUsefulFeatures   badState
  addNewlyUsefulCandidates badState

addNewlyUsefulFeatures :: CIConstraints t => ProgState t -> CiM t ()
addNewlyUsefulFeatures newBadState = do
  features          <- getFeatures
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  let toFeaturePair feature = do
        rejected <- getFeatureRejectedBads feature
        pure $ (feature, rejected)
  featuresList <- mapM toFeaturePair $ Set.toList features
  let useful (feature, rejectedBads) = do
        pure $ (Set.member newBadState rejectedBads)
            && (not $ any (Set.isProperSubsetOf (featAcceptedGoods feature)) rootClauseAccepts)
  newlyUseful <- filterM useful featuresList
  mapM_ (uncurry seedFeature) newlyUseful

addNewlyUsefulCandidates :: CIConstraints t => ProgState t -> CiM t ()
addNewlyUsefulCandidates newBadState = do
  featureCandidates <- getFeatureCandidates
  let rejectsNewBad assertion = do
        result <- lift $ testState assertion newBadState
        pure $ if result then Left assertion else Right assertion
  (candidates', newlyUseful) <- pure . partitionEithers =<< mapM rejectsNewBad featureCandidates
  maybeUseful <- mapM assertionToFeature newlyUseful
  let newFeatures = filter (not . Set.null . featAcceptedGoods . fst) maybeUseful

  -- Remember the new features so we don't have do duplicate the SMT work,
  -- but only actually enqueue the ones who accept new states.
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  let useful (feature, _) = not $ (any (Set.isProperSubsetOf (featAcceptedGoods feature)) rootClauseAccepts)
  let featuresToSeed = filter useful newFeatures

  putFeatureCandidates candidates'
  mapM_ (uncurry addFeature) newFeatures
  mapM_ (uncurry seedFeature) featuresToSeed

seedFeature :: CIConstraints t => Feature t -> Set (ProgState t) -> CiM t ()
seedFeature feature rejectedBads = do
  badStates <- getBadStates
  if (Set.isSubsetOf badStates rejectedBads)
    then addRootClause (Clause [feature] (featAcceptedGoods feature))
    else enqueue $ featureToEntry feature rejectedBads


-- Update Mechanics:

data UpdateFlag = Accepts
                | Rejects
                deriving (Ord, Eq, Show)

isRejects :: UpdateFlag -> Bool
isRejects = (== Rejects)

tagFeature :: CIConstraints t => ProgState t -> Feature t -> CiM t (Feature t, UpdateFlag)
tagFeature newBadState feature = do
  acceptsNewBad <- lift $ testState (featAssertion feature) newBadState
  let flag = if acceptsNewBad then Accepts else Rejects
  pure (feature, flag)

tagClause :: CIConstraints t => ProgState t -> Clause t -> CiM t (Clause t, UpdateFlag)
tagClause newBadState clause = do
  let features = clauseFeatures clause
  (_, updateFlags) <- pure . unzip =<< mapM (tagFeature newBadState) features
  let flag = if any isRejects updateFlags then Rejects else Accepts
  pure (clause, flag)

updateRootClauses :: CIConstraints t => ProgState t -> [RootClause t] -> CiM t [RootClause t]
updateRootClauses newBadState rootClauses = do
  -- Collect and update all clauses, throw away now-bad clauses, and rebuild the tree.
  let collectClauses (RootClause clause covers) = clause:(concat . map collectClauses $ covers)
  let allClauses = concat . map collectClauses $ rootClauses
  -- To throw away clauses altogether:
  -- let allClauses = map rcClause rootClauses
  updatedClauses <- pure
                  . map fst
                  . filter (isRejects . snd)
                  =<< mapM (tagClause newBadState) allClauses
  pure $ foldr insertRootClause [] updatedClauses

updateFeatureCache :: CIConstraints t => ProgState t -> FeatureCache t -> CiM t (FeatureCache t)
updateFeatureCache newBadState (FeatureCache features rejByFeature featByAccepted featByRejected) = do
  featuresToUpdate <- pure
                    . map fst
                    . filter (isRejects . snd)
                    =<< mapM (tagFeature newBadState) (Set.toList features)
  let updatedSet feature rejMap = case Map.lookup feature rejMap of
        Nothing  -> Set.singleton newBadState
        Just set -> Set.insert newBadState set
  let updateRej feature rejMap = Map.insert feature (updatedSet feature rejMap) rejMap
  let rejByFeature' = foldr updateRej rejByFeature featuresToUpdate
  let rejectorSet = Set.fromList featuresToUpdate
  let featByRejected' = Map.insert newBadState rejectorSet featByRejected
  pure $ FeatureCache features rejByFeature' featByAccepted featByRejected'

updateEntry :: CIConstraints t => ProgState t -> Entry t -> CiM t (Entry t)
updateEntry newBadState (Entry candidate rejected accepted) = do
  (candidate', updateFlags) <- pure . unzip =<< mapM (tagFeature newBadState) candidate
  let rejected' = if any isRejects updateFlags
                  then Set.insert newBadState rejected
                  else rejected
  pure $ Entry candidate' rejected' accepted

updateQueue :: CIConstraints t => ProgState t -> Queue t -> CiM t (Queue t)
updateQueue newBadState queue = do
  let entries = Set.toList . Set.unions . Map.elems $ queue
  updatedEntries <- mapM (updateEntry newBadState) entries
  pure $ foldr qInsert Map.empty updatedEntries


-----------------------
-- Entry Conversions --
-----------------------

featureToEntry :: Feature t -> Set (ProgState t) -> Entry t
featureToEntry feature rejectedBads = Entry [feature] rejectedBads (featAcceptedGoods feature)

assertionToFeature :: CIConstraints t => Assertion t -> CiM t (Feature t, Set (ProgState t))
assertionToFeature assertion = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  (acceptedGoods, _) <- lift $ splitStates assertion $ Set.toList goodStates
  (_, rejectedBads)  <- lift $ splitStates assertion $ Set.toList badStates
  pure $ (Feature assertion $ Set.fromList acceptedGoods, Set.fromList rejectedBads)


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


extractState :: CIConstraints t => Assertion t -> CiM t (ProgState t)
extractState assertion = do
  stateNames <- getStateNames
  pure $ closeNames stateNames $ extractState' assertion

-- TODO: This is fragile.
extractState' :: Pretty t => Assertion t -> ProgState t
extractState' assertion = case assertion of
  Eq lhs rhs -> Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> Map.unions $ map extractState' as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith
