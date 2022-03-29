{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Orhle.CInvGen
  ( Configuration(..)
  , Job(..)
  , cInvGen

  -- Exposed for testing:
  , BadState(..)
  , CIEnv(..)
  , CiM
  , Clause(..)
  , Entry(..)
  , Feature(..)
  , FeatureCache(..)
  , GoodState(..)
  , Queue(..)
  , RootClause(..)
  , States(..)
  , UpdateFlag(..)
  , addNewlyUsefulCandidates
  , buildCurrentResult
  , closeNames
  , entryScore
  , fcAddFeature
  , fcEmpty
  , getFeatureIds
  , getFeatureCache
  , getFeatureCandidates
  , getFeatures
  , getRemainingGoods
  , getRootClauses
  , getQueue
  , learnSeparator
  , mkCIEnv
  , mkStates
  , putRootClauses
  , qEmpty
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
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
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

------------
-- States --
------------

type GoodStateId = Int
type GoodStateIdSet = IntSet

data GoodState t = GoodState
  { gsId    :: GoodStateId
  , gsState :: ProgState t
  } deriving (Eq, Ord)

type BadStateId = Int
type BadStateIdSet = IntSet

data BadState t = BadState
  { bsId    :: BadStateId
  , bsState :: ProgState t
  } deriving (Eq, Ord)

instance Pretty t => Pretty (BadState t) where
  pretty (BadState _ state) = pretty state

data States t = States
  { stNextBsId     :: Int
  , stBadStateIds  :: BadStateIdSet
  , stBadStates    :: Set (BadState t)
  , stGoodStateIds :: GoodStateIdSet
  , stGoodStates   :: Set (GoodState t)
  }

mkStates :: Set (BadState t) -> Set (GoodState t) -> States t
mkStates bads goods =
  let
    badIds   = map bsId $ Set.toList bads
    goodIds  = map gsId $ Set.toList goods
    maxBadId = foldr (\x y -> if x >= y then x else y) (-1) badIds
    nextBsId = maxBadId + 1
  in States nextBsId (IntSet.fromList badIds) bads (IntSet.fromList goodIds) goods

stAddBadState :: Ord t => ProgState t -> States t -> (BadState t, States t)
stAddBadState state (States nextBsId badIds bads goodIds goods) =
  let
    badState = BadState nextBsId state
    badIds'  = IntSet.insert (nextBsId) badIds
    bads'    = Set.insert badState bads
  in (badState, States (nextBsId + 1) badIds' bads' goodIds goods)


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
  , fcFeaturesById       :: Map FeatureId  (Feature t)
  , fcRejectedByFeature  :: Map FeatureId  BadStateIdSet
  , fcFeaturesByAccepted :: Map FeatureId  GoodStateIdSet
  , fcFeaturesByRejected :: Map BadStateId FeatureIdSet
  }

fcEmpty :: FeatureCache t
fcEmpty = FeatureCache 0 IntSet.empty Map.empty Map.empty Map.empty Map.empty

fcIncrementId :: FeatureCache t -> (FeatureId, FeatureCache t)
fcIncrementId (FeatureCache nextId fids fById rejByFeat featByAcc featByRej) =
  (nextId, FeatureCache (nextId + 1) fids fById rejByFeat featByAcc featByRej)

fcAddFeature :: Ord t => Feature t -> BadStateIdSet -> FeatureCache t -> FeatureCache t
fcAddFeature feature rejected (FeatureCache nextId featureIds featuresById rejectedByFeature featsByAccepted featsByRejected) =
  let
    featureId             = featId feature
    nextId'               = if featureId < nextId then nextId else featureId + 1
    featureIds'           = IntSet.insert featureId featureIds
    featuresById'         = Map.insert featureId feature featuresById
    rejectedByFeature'    = Map.insert featureId rejected rejectedByFeature
    featInsert stId stMap = case Map.lookup stId stMap of
                              Nothing  -> Map.insert stId (IntSet.singleton featureId)  stMap
                              Just set -> Map.insert stId (IntSet.insert featureId set) stMap
    featsByAccepted'      = foldr featInsert featsByAccepted $ IntSet.toList (featAcceptedGoods feature)
    featsByRejected'      = foldr featInsert featsByRejected $ IntSet.toList rejected
  in
    if featureId `IntSet.member` featureIds
    then error $ "Feature ID already in use: " ++ (show featureId)
    else FeatureCache nextId' featureIds' featuresById' rejectedByFeature' featsByAccepted' featsByRejected'

fcLookupFeature :: FeatureCache t -> FeatureId -> Feature t
fcLookupFeature fc featureId = case Map.lookup featureId $ fcFeaturesById fc of
  Nothing      -> error $ "Feature ID not found: " ++ show featureId
  Just feature -> feature

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


-------------
-- Clauses --
-------------

data Clause t = Clause
  { clauseFeatures      :: FeatureIdSet
  , clauseAcceptedGoods :: GoodStateIdSet
  } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Clause t) where
  pretty (Clause features accepted) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Features:" <+> pretty (IntSet.toList features)
    , pretty "Clause accepts:" <+> pretty (IntSet.toList accepted)
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

rootClauseAcceptedGoods :: RootClause t -> GoodStateIdSet
rootClauseAcceptedGoods (RootClause clause _) = clauseAcceptedGoods clause

rootClauseAssertion :: FeatureCache t -> RootClause t -> Assertion t
rootClauseAssertion featureCache (RootClause clause _) =
  aAnd . map (featAssertion . fcLookupFeature featureCache) . IntSet.toList . clauseFeatures $ clause


------------------
-- Seach Queues --
------------------

data Queue t = Queue
  { qQueue :: Map Int (Set (Entry t))
  , qSeen  :: Set FeatureIdSet
  } deriving (Ord, Eq, Show)

data Entry t = Entry
  { entryCandidate     :: FeatureIdSet
  , entryRejectedBads  :: BadStateIdSet
  , entryAcceptedGoods :: GoodStateIdSet
  } deriving (Ord, Show)

-- TODO: Is this actually a good idea?
instance Ord t => Eq (Entry t) where
  entry1 == entry2 = entryCandidate entry1 == entryCandidate entry2

instance Pretty t => Pretty (Entry t) where
  pretty (Entry candidate rejected accepted) = align $
        pretty "Candidate["
    <>  pretty (IntSet.size accepted)
    <>  pretty "/"
    <>  pretty (IntSet.size rejected)
    <>  pretty "]:"
    <+> pretty (IntSet.toList candidate)

qEmpty :: Queue t
qEmpty = Queue Map.empty Set.empty

qSize :: Queue t -> Int
qSize (Queue queue _) = Map.foldr (\set count -> count + Set.size set) 0 queue

qInsert :: CIConstraints t => Entry t -> Queue t -> Queue t
qInsert entry (Queue queue seen) =
  let
    score = entryScore entry
    candidate = entryCandidate entry
    seen' = Set.insert candidate seen
  in case (Set.member candidate seen, Map.lookup score queue) of
    (True, _)        -> Queue queue seen
    (_   , Nothing)  -> Queue (Map.insert score (Set.singleton entry) queue) seen'
    (_   , Just set) -> Queue (Map.insert score (Set.insert entry set) queue) seen'

qPop :: Queue t -> (Maybe (Entry t), Queue t)
qPop (Queue queue seen) = do
  let mMaxView = Map.maxViewWithKey queue
  case mMaxView of
    Nothing -> (Nothing, Queue queue seen)
    Just ((key, maxSet), queue') ->
      let mMaxElt = Set.maxView maxSet
      in case mMaxElt of
        Nothing -> (Nothing, Queue queue' seen)
        Just (elt, maxSet') ->
          if Set.null maxSet'
          then (Just elt, Queue queue' seen)
          else (Just elt, Queue (Map.insert key maxSet' queue') seen)


-------------------
-- Cost Function --
-------------------

entryScore :: CIConstraints t => Entry t -> Int
entryScore (Entry candidate rejectedBads acceptedGoods) =
  let
    numRejected   = IntSet.size rejectedBads
    candidateSize = IntSet.size candidate
    acceptedSize  = IntSet.size acceptedGoods
  in (acceptedSize * numRejected) `div` candidateSize


-----------------------
-- Computation Monad --
-----------------------

data CIEnv t = CIEnv { envQueue             :: Queue t
                     , envStates            :: States t
                     , envRootClauses       :: [RootClause t]
                     , envRootsAccepted     :: GoodStateIdSet
                     , envFeatureCache      :: FeatureCache t
                     , envFeatureCandidates :: [Assertion t]
                     , envGoalQuery         :: Assertion t -> Ceili (Assertion t)
                     , envStateNames        :: [Name]
                     , envMaxClauseSize     :: Int
                     , envClauseDenylist    :: Set FeatureIdSet
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
    badStates           = Set.fromList . map (uncurry BadState)  $ zip [0..] (Set.toList closedBads)
    goodStates          = Set.fromList . map (uncurry GoodState) $ zip [0..] (Set.toList closedGoods)
    states              = mkStates badStates goodStates
    fCandidates         = Set.toList $ (cfgFeatureGenerator config) (cfgMaxFeatureSize config)
    loopCond            = jobLoopCond job
    negLoopCond         = Not $ loopCond
    maxClauseSize       = cfgMaxClauseSize config
    goalQuery candidate = do
      weakestPre <- (cfgWpSemantics config) (cfgWpContext config) (jobLoopBody job) candidate
      pure $ aAnd [ Imp (aAnd [candidate, negLoopCond]) (jobPostCond job) -- Establishes Post
                  , Imp (aAnd [candidate, loopCond]) weakestPre           -- Inductive
                  ]
  in CIEnv qEmpty states [] IntSet.empty fcEmpty fCandidates goalQuery names maxClauseSize Set.empty

getQueue :: CiM t (Queue t)
getQueue = get >>= pure . envQueue

getBadStates :: CiM t (Set (BadState t))
getBadStates = get >>= pure . stBadStates . envStates

getBadStateIds :: CiM t BadStateIdSet
getBadStateIds = get >>= pure . stBadStateIds . envStates

getGoodStates :: CiM t (Set (GoodState t))
getGoodStates = get >>= pure . stGoodStates . envStates

getGoodStateIds :: CiM t GoodStateIdSet
getGoodStateIds = get >>= pure . stGoodStateIds . envStates

getRootClauses :: CiM t [RootClause t]
getRootClauses = get >>= pure . envRootClauses

getRootsAccepted :: CiM t GoodStateIdSet
getRootsAccepted = get >>= pure . envRootsAccepted

getFeatureCache :: CiM t (FeatureCache t)
getFeatureCache = get >>= pure . envFeatureCache

getFeatureIds :: CiM t FeatureIdSet
getFeatureIds = get >>= pure . fcFeatureIds . envFeatureCache

getFeatures :: CiM t [Feature t]
getFeatures = do
  fc <- getFeatureCache
  pure $ Map.elems (fcFeaturesById fc)

nextFeatureId :: CiM t FeatureId
nextFeatureId = do
  fc <- getFeatureCache
  let (nextId, fc') = fcIncrementId fc
  putFeatureCache fc'
  pure nextId

getFeatureRejectedBads :: Ord t => FeatureId -> CiM t BadStateIdSet
getFeatureRejectedBads feature = do
  cache <- getFeatureCache
  pure $ fcRejectedBads feature cache

getFeaturesWhichAccept :: Ord t => [GoodStateId] -> CiM t [FeatureIdSet]
getFeaturesWhichAccept states = do
  cache <- getFeatureCache
  pure $ fcFeaturesWhichAccept states cache

getFeaturesWhichReject :: Ord t => [BadStateId] -> CiM t [FeatureIdSet]
getFeaturesWhichReject states = do
  cache <- getFeatureCache
  pure $ fcFeaturesWhichReject states cache

getFeatureCandidates :: CiM t [Assertion t]
getFeatureCandidates = get >>= pure . envFeatureCandidates

lookupFeature :: FeatureId -> CiM t (Feature t)
lookupFeature featureId = do
  fc <- getFeatureCache
  pure $ fcLookupFeature fc featureId

lookupFeatures :: [FeatureId] -> CiM t [Feature t]
lookupFeatures featureIds = do
  fc <- getFeatureCache
  pure $ map (fcLookupFeature fc) featureIds

getMaxClauseSize :: CiM t Int
getMaxClauseSize = get >>= pure . envMaxClauseSize

getStateNames :: CiM t [Name]
getStateNames = get >>= pure . envStateNames

putQueue :: Queue t -> CiM t ()
putQueue queue = do
  CIEnv _ states roots rootsAccepted features fCandidates goalQ names mcs denylist <- get
  put $ CIEnv queue states roots rootsAccepted features fCandidates goalQ names mcs denylist

addBadState :: Ord t => ProgState t -> CiM t (BadState t)
addBadState state = do
  CIEnv queue states roots rootsAccepted features fCandidates goalQ names mcs denylist <- get
  let (badState, states') = stAddBadState state states
  put $ CIEnv queue states' roots rootsAccepted features fCandidates goalQ names mcs denylist
  pure badState

putRootClauses :: Ord t => [RootClause t] -> CiM t ()
putRootClauses roots = do
  CIEnv queue states _ _ features fCandidates goalQ names mcs denylist <- get
  let accepted = IntSet.unions $ map rootClauseAcceptedGoods roots
  put $ CIEnv queue states roots accepted features fCandidates goalQ names mcs denylist

putFeatureCache :: FeatureCache t -> CiM t ()
putFeatureCache featureCache = do
  CIEnv queue states roots rootsAccepted _ fCandidates goalQ names mcs denylist <- get
  put $ CIEnv queue states roots rootsAccepted featureCache fCandidates goalQ names mcs denylist

putFeatureCandidates :: [Assertion t] -> CiM t ()
putFeatureCandidates fCandidates = do
  CIEnv queue states roots rootsAccepted features _ goalQ names mcs denylist <- get
  put $ CIEnv queue states roots rootsAccepted features fCandidates goalQ names mcs denylist

addFeature :: Ord t => Feature t -> BadStateIdSet -> CiM t ()
addFeature feature rejected = do
  CIEnv queue states roots rootsAccepted featureCache fCandidates goalQ names mcs denylist <- get
  let featureCache' = fcAddFeature feature rejected featureCache
  put $ CIEnv queue states roots rootsAccepted featureCache' fCandidates goalQ names mcs denylist

denyClause :: FeatureIdSet -> CiM t ()
denyClause clause = do
  CIEnv queue states roots rootsAccepted featureCache fCandidates goalQ names mcs denylist <- get
  let denylist' = Set.insert clause denylist
  put $ CIEnv queue states roots rootsAccepted featureCache fCandidates goalQ names mcs denylist'

isDenied :: FeatureIdSet -> CiM t Bool
isDenied clause = do
  denylist <- get >>= pure . envClauseDenylist
  pure $ Set.member clause denylist

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
  origQueue <- getQueue
  origRoots <- getRootClauses
  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> clog_d "[CInvGen] Unable to find separator." >> pure Nothing
    Just (separator, clauses) -> do
      clog_d . show $ pretty "[CInvGen] Candidate precondition:" <+> (align . pretty) separator
      goalStatus <- checkGoal separator
      case goalStatus of
        GoalCex cex -> do
          clog_d . show $ pretty "[CInvGen] Found counterexample:" <+> (align . pretty) cex
          putQueue qEmpty
          putRootClauses []
          addCounterexample cex
          cInvGen'
        GoalMet -> do
          clog_d . show $ pretty "[CInvGen] Found invariant:" <+> (align . pretty) separator
          pure $ Just separator
        SMTError msg -> do
          clog_e . show $ pretty "[CInvGen]" <+> pretty msg
                      <+> pretty "on candidate" <+> (align . pretty) separator
          -- throwError "SMT error"
          --cInvGen' -- Continue now that the problematic assertion is out of the queue.
          mapM_ denyClause $ map clauseFeatures clauses
          putRootClauses origRoots
          putQueue origQueue
          cInvGen'

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

learnSeparator :: CIConstraints t => CiM t (Maybe (Assertion t, [Clause t]))
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
    then do clog_d "[CInvGen] No bad states, returning true."; pure $ Just (ATrue, [])
  else if Set.null goodStates
    then do clog_d "[CInvGen] No good states, returning false."; pure $ Just (AFalse, [])
  else learnSeparator'

learnSeparator' :: CIConstraints t => CiM t (Maybe (Assertion t, [Clause t]))
learnSeparator' = do
  remaining <- getRemainingGoods
  if IntSet.null remaining
    then do
      assertion <- buildCurrentResult
      clauses <- pure . map rcClause =<< getRootClauses
      pure $ Just (assertion, clauses)
    else do
      mEntry <- dequeue
      case mEntry of
        Nothing -> do
          clog_d $ "[CInvGen] Search queue is empty, failing."
          --printSeen
          pure Nothing
        Just entry -> do
          maxClauseSize <- getMaxClauseSize
          if IntSet.size (entryCandidate entry) >= maxClauseSize
            then learnSeparator'
            else do
              nextFeatures <- usefulFeatures entry
              queue <- getQueue
              clog_d $ "[CInvGen] Candidate: " ++ (show $ entryCandidate entry)
              clog_d $ "[CInvGen] Useful features: " ++ (show $ length nextFeatures) ++ ", queue size: " ++ (show $ qSize queue)
              enqueueNextLevel entry nextFeatures
              learnSeparator'

printSeen :: Pretty t => CiM t ()
printSeen = do
  seenIds <- getQueue >>= pure . (map IntSet.toList) . Set.toList . qSeen
  seenFeatures <- mapM lookupFeatures seenIds
  let seenAssertions = map (aAnd . map featAssertion) seenFeatures
  clog_d . show $ pretty "Seen features:" <+> pretty seenAssertions

-- (<= (+ original!sum (* -1 refinement!sum)) 0)

target1 :: Assertion Integer
target1 = Lte (Add [Var $ Name "original!sum" 0, Mul [Num (-1), Var $ Name "refinement!sum" 0] ]) (Num 0)

target2 :: Assertion Integer
target2 = Lte (Add [Mul [Num (-1), Var $ Name "original!sum" 0], Var $ Name "refinement!sum" 0 ]) (Num 0)

arithSE :: (Embeddable b a, Eq a) => Arith a -> Arith b -> Bool
arithSE arithA arithB = case (arithA, arithB) of
  (Var a, Var b) -> a == b
  (Num a, Num b) -> a == embed b
  (Add as, Add bs) -> all (uncurry arithSE) (zip as bs)
  (Mul as, Mul bs) -> all (uncurry arithSE) (zip as bs)
  _ -> False

structurallyEqual :: (Embeddable b a, Eq a) => Assertion a -> Assertion b -> Bool
structurallyEqual assertionA assertionB =
  case (assertionA, assertionB) of
    (Lte al ar, Lte bl br) -> arithSE al bl && arithSE ar br
    _ -> False

checkForTargets ids = do
  if IntSet.size ids <= 2
    then do
    assertions <- lookupFeatures (IntSet.toList ids) >>= pure . map featAssertion
    case assertions of
      [ca] | structurallyEqual ca target1 -> pure (True, False)
      [ca] | structurallyEqual ca target2 -> pure (False, True)
      [ca1, ca2] | structurallyEqual ca1 target1 && structurallyEqual ca2 target2 -> pure (True, True)
      [ca1, ca2] | structurallyEqual ca1 target2 && structurallyEqual ca2 target1 -> pure (True, True)
      _ -> pure (False, False)
    else pure (False, False)

usefulFeatures :: CIConstraints t => Entry t -> CiM t [FeatureId]
usefulFeatures (Entry candidate enRejectedBads enAcceptedGoods) = do
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
--  (t1, t2) <- checkForTargets candidate
--  if t1 then clog_d $ "Finding useful features for " ++ (show . pretty $ target1) else pure ()
--  if t2 then clog_d $ "Finding useful features for " ++ (show . pretty $ target2) else pure ()
  if any (enAcceptedGoods `IntSet.isProperSubsetOf`) $ rootClauseAccepts
    then do
      -- if (t1 || t2)
      --   then clog_d "Short circuiting"
      --   else pure ()
      pure [] -- Short circuit if there are no possible useful features.
    else do
    case IntSet.null candidate of
      True -> error "Empty candidate"
      _ ->  do
        -- A useful addition to an existing candidate rejects something new
        -- while not bringing the accepted states for the new candidate
        -- down to a subset of of the good states already accepted by the
        -- entry's clauses.
        acceptsSomethingGood <- do
          let rootAcceptSet = IntSet.unions rootClauseAccepts
          let interestingGoods = IntSet.toList $ IntSet.difference enAcceptedGoods rootAcceptSet
          pure . IntSet.unions =<< getFeaturesWhichAccept interestingGoods
        rejectsSomethingBad <- do
          badStateIds <- getBadStateIds
          let remainingBads = IntSet.difference badStateIds enRejectedBads
          pure . IntSet.unions =<< getFeaturesWhichReject (IntSet.toList remainingBads)
        -- if (t1 || t2)
        --   then do
        --     goodFeats <- lookupFeatures $ IntSet.toList acceptsSomethingGood
        --     badFeats <- lookupFeatures $ IntSet.toList rejectsSomethingBad
        --     clog_d $ "Accepts good: " ++ (show . pretty $ goodFeats)
        --     clog_d $ "Rejects bad: " ++ (show . pretty $ badFeats)
        --   else pure ()
        pure . IntSet.toList $ IntSet.intersection rejectsSomethingBad acceptsSomethingGood

enqueueNextLevel :: CIConstraints t => Entry t -> [FeatureId] -> CiM t ()
enqueueNextLevel _ [] = pure ()
enqueueNextLevel entry@(Entry candidate enRejectedBads _) (newFeature:rest) = do
  let newCandidateIds = IntSet.insert newFeature candidate
  --(t1, t2) <- checkForTargets newCandidateIds
  --if t1 && t2 then clog_d "**** See target in enqueueNextLevel" else pure ()
  denied <- isDenied newCandidateIds
  if denied
    then do
      --if t1 && t2 then clog_d "**** No stairway?! Denied!" else pure ()
      enqueueNextLevel entry rest
    else do
      newCandidateFeatures <- lookupFeatures $ IntSet.toList newCandidateIds
      -- A useful feature *optimistically* accepted an interesting set of good
      -- states, but now we will do the SMT work to make sure.
      rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses

      goodStates <- getGoodStates
      let newCandidateAssertion = aAnd $ map featAssertion newCandidateFeatures
      (newAcceptedGoodsList, _) <- lift $ splitGoodStates newCandidateAssertion $ Set.toList goodStates
      let newAcceptedGoods = IntSet.fromList $ map gsId newAcceptedGoodsList

      if (any (newAcceptedGoods `IntSet.isProperSubsetOf`) rootClauseAccepts)
        then do
        -- It turns out the accepted good states are not intersting.
        -- if t1 && t2 then do
        --   clog_d "**** New goods are a proper subset of root clauses"
        --   newFeat <- lookupFeature newFeature
        --   entryFeat <- lookupFeatures $ IntSet.toList candidate
        --   clog_d $ "**** entryFeature: " ++ (show . pretty $ entryFeat)
        --   clog_d $ "**** newFeature: " ++ (show . pretty $ newFeat)
        --   clog_d $ "**** assertion: " ++ (show . pretty $ newCandidateAssertion)
        --   clog_d $ "**** rootClauseAccepts: " ++ (show . pretty . map IntSet.toList $ rootClauseAccepts)
        --   clog_d $ "**** newAcceptedGoods: " ++ (show . pretty . IntSet.toList $ newAcceptedGoods)
        --   clog_d $ "**** goodStates: " ++ (show . pretty $ (map (\(GoodState sid st) -> (sid, st)) $ Set.toList goodStates))
        --   else pure ()
        enqueueNextLevel entry rest
        else do
          badStateIds <- getBadStateIds
          featureRejectedBads <- getFeatureRejectedBads newFeature
          let newRejectedBads = IntSet.union enRejectedBads featureRejectedBads
          -- if t1 && t2
          --   then do
          --     newFeat <- lookupFeature newFeature
          --     entryFeat <- lookupFeatures $ IntSet.toList candidate
          --     clog_d $ "**** entryFeature: " ++ (show . pretty $ entryFeat)
          --     clog_d $ "**** newFeature: " ++ (show . pretty $ newFeat)
          --     clog_d $ "**** enRejectedBads: " ++ (show . pretty . IntSet.toList $ enRejectedBads)
          --     clog_d $ "**** featureRejectedBads: " ++ (show . pretty . IntSet.toList $ featureRejectedBads)
          --     clog_d $ "**** bads: " ++ (show . pretty . IntSet.toList $ badStateIds)
          --     let diff = IntSet.difference badStateIds newRejectedBads
          --     badStates <- getBadStates >>= pure . Set.toList
          --     let diffStates = filter (\st -> bsId st `IntSet.member` diff) badStates
          --     clog_d $ "**** difference: " ++ (show . pretty $ diffStates)
          --   else pure ()

          if newRejectedBads == badStateIds
            then do
              -- We found a new root clause.
              addRootClause $ Clause newCandidateIds newAcceptedGoods
              --if t1 && t2 then clog_d "**** Target added as root clause (yay)" else pure ()
              enqueueNextLevel entry rest
            else do
              enqueue $ Entry newCandidateIds newAcceptedGoods newRejectedBads
              --if t1 && t2 then clog_d "**** Target enqueued (boo)" else pure ()
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

    checkDuplicate rclause = (clauseFeatures newClause) == (clauseFeatures rclause)
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
isCoveredBy clause1 clause2 = IntSet.isProperSubsetOf (clauseAcceptedGoods clause1) (clauseAcceptedGoods clause2)


---------------------------
-- Counterexample Update --
---------------------------

addCounterexample :: CIConstraints t => ProgState t -> CiM t ()
addCounterexample cexState = do
  -- Note: we don't eagerly flush entries which no longer cover good states
  -- outside the root clause accepted goods. Instead, this check is done
  -- for all entries in learnSeparator / usefulFeatures.
  badState <- addBadState cexState
  getFeatureCache >>= updateFeatureCache badState >>= putFeatureCache
  getRootClauses  >>= updateRootClauses  badState >>= putRootClauses
  getQueue        >>= updateQueue        badState >>= putQueue
  addNewlyUsefulFeatures   badState
  addNewlyUsefulCandidates badState

addNewlyUsefulFeatures :: CIConstraints t => BadState t -> CiM t ()
addNewlyUsefulFeatures newBadState = do
  features <- getFeatures
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  let toFeaturePair feature = do
        rejected <- getFeatureRejectedBads (featId feature)
        pure $ (feature, rejected)
  let useful (feature, rejectedBads) = do
        let acceptedGoods = featAcceptedGoods feature
        pure $ (IntSet.member (bsId newBadState) rejectedBads)
            && (not $ any (acceptedGoods `IntSet.isProperSubsetOf`) rootClauseAccepts)
  featuresList <- mapM toFeaturePair features
  newlyUseful  <- filterM useful featuresList
  mapM_ (uncurry seedFeature) newlyUseful

addNewlyUsefulCandidates :: CIConstraints t => BadState t -> CiM t ()
addNewlyUsefulCandidates newBadState = do
  featureCandidates <- getFeatureCandidates
  let rejectsNewBad assertion = do
        result <- lift $ testState assertion (bsState newBadState)
        case result of
          Accepted -> pure $ Left assertion
          Rejected -> pure $ Right assertion
          Error err -> do
            clog_e . show $ pretty "SMT error evaluating feature candidate"
                        <+> pretty assertion <> pretty ":"
                        <+> pretty err <> pretty "."
                        <+> pretty "Ignoring candidate."
            pure $ Left assertion
  (candidates', newlyUseful) <- pure . partitionEithers =<< mapM rejectsNewBad featureCandidates
  maybeUseful <- mapM assertionToFeature newlyUseful
  let newFeatures = filter (not . IntSet.null . featAcceptedGoods . fst) maybeUseful

  -- Remember the new features so we don't have do duplicate the SMT work,
  -- but only actually enqueue the ones who accept new states.
  rootClauseAccepts <- pure . map (clauseAcceptedGoods . rcClause) =<< getRootClauses
  let useful (feature, _) = not $ (any (IntSet.isProperSubsetOf (featAcceptedGoods feature)) rootClauseAccepts)
  let featuresToSeed = filter useful newFeatures

  putFeatureCandidates candidates'
  mapM_ (uncurry addFeature) newFeatures
  mapM_ (uncurry seedFeature) featuresToSeed

seedFeature :: CIConstraints t => Feature t -> BadStateIdSet -> CiM t ()
seedFeature feature rejectedBads = do
  badStateIds <- getBadStateIds
  if (IntSet.isSubsetOf badStateIds rejectedBads)
    then addRootClause (Clause (IntSet.singleton $ featId feature) (featAcceptedGoods feature))
    else enqueue $ featureToEntry feature rejectedBads


-- Update Mechanics:

data UpdateFlag = Accepts
                | Rejects
                deriving (Ord, Eq, Show)

isRejects :: UpdateFlag -> Bool
isRejects = (== Rejects)

isAccepts :: UpdateFlag -> Bool
isAccepts = (== Accepts)

tagFeature :: CIConstraints t => BadState t -> Feature t -> CiM t (Feature t, UpdateFlag)
tagFeature newBadState feature = do
  acceptsNewBad <- lift $ testState (featAssertion feature) (bsState newBadState)
  let flag = case acceptsNewBad of
        Accepted -> Accepts
        Rejected -> Rejects
        Error _  -> Accepts -- Pessimistically assume does not reject the new bad state.
  pure (feature, flag)

tagClause :: CIConstraints t => BadState t -> Clause t -> CiM t (Clause t, UpdateFlag)
tagClause newBadState clause = do
  features <- lookupFeatures $ IntSet.toList $ clauseFeatures clause
  (_, updateFlags) <- pure . unzip =<< mapM (tagFeature newBadState) features
  let flag = if any isRejects updateFlags then Rejects else Accepts
  pure (clause, flag)

updateRootClauses :: CIConstraints t => BadState t -> [RootClause t] -> CiM t [RootClause t]
updateRootClauses newBadState rootClauses = do
  -- Collect and update all clauses, throw away now-bad clauses, and rebuild the tree.
  let collectClauses (RootClause clause covers) = clause:(concat . map collectClauses $ covers)
  let allClauses = concat . map collectClauses $ rootClauses
  taggedClauses <- mapM (tagClause newBadState) allClauses
  let updatedClauses = map fst
                     . filter (isRejects . snd)
                     $ taggedClauses
  -- let reenqueue (Clause features acceptedGoods) = do
  --       rejectedBads <- mapM getFeatureRejectedBads (IntSet.toList features)
  --       enqueue $ Entry features (IntSet.unions rejectedBads) acceptedGoods
  -- mapM_ reenqueue $ map fst . filter (isAccepts . snd) $ taggedClauses
  pure $ foldr insertRootClause [] updatedClauses

updateFeatureCache :: CIConstraints t => BadState t -> FeatureCache t -> CiM t (FeatureCache t)
updateFeatureCache newBadState (FeatureCache nextId featureIds featuresById rejByFeature featByAccepted featByRejected) = do
  let newBadStateId = bsId newBadState
  rejectingFeatures <- pure
                     . map featId
                     . map fst
                     . filter (isRejects . snd)
                     =<< mapM (tagFeature newBadState) (Map.elems featuresById)
  let updatedSet featureId rejMap = case Map.lookup featureId rejMap of
        Nothing  -> IntSet.singleton newBadStateId
        Just set -> IntSet.insert newBadStateId set
  let updateRej featureId rejMap = Map.insert featureId (updatedSet featureId rejMap) rejMap
  let rejByFeature' = foldr updateRej rejByFeature rejectingFeatures
  let featByRejected' = Map.insert newBadStateId (IntSet.fromList rejectingFeatures) featByRejected
  pure $ FeatureCache nextId featureIds featuresById rejByFeature' featByAccepted featByRejected'

updateEntry :: CIConstraints t => BadState t -> Entry t -> CiM t (Entry t)
updateEntry newBadState (Entry candidateIds rejected accepted) = do
  let newBadStateId = bsId newBadState
  candidate <- lookupFeatures $ IntSet.toList candidateIds
  (candidate', updateFlags) <- pure . unzip =<< mapM (tagFeature newBadState) candidate
  let candidateIds' = IntSet.fromList $ map featId candidate'
  let rejected' = if any isRejects updateFlags
                  then IntSet.insert newBadStateId rejected
                  else rejected
  pure $ Entry candidateIds' rejected' accepted

updateQueue :: CIConstraints t => BadState t -> Queue t -> CiM t (Queue t)
updateQueue newBadState queue = do
  let entries = Set.toList . Set.unions . Map.elems . qQueue $ queue
  updatedEntries <- mapM (updateEntry newBadState) entries
  pure $ foldr qInsert qEmpty updatedEntries


-----------------------
-- Entry Conversions --
-----------------------

featureToEntry :: Feature t -> BadStateIdSet -> Entry t
featureToEntry feature rejectedBads = Entry (IntSet.singleton $ featId feature) rejectedBads (featAcceptedGoods feature)

assertionToFeature :: CIConstraints t => Assertion t -> CiM t (Feature t, BadStateIdSet)
assertionToFeature assertion = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  (acceptedGoods, _) <- lift $ splitGoodStates assertion $ Set.toList goodStates
  (_, rejectedBads)  <- lift $ splitBadStates  assertion $ Set.toList badStates
  featureId <- nextFeatureId
  pure $ (Feature featureId assertion (IntSet.fromList $ map gsId acceptedGoods), (IntSet.fromList $ map bsId rejectedBads))


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

getRemainingGoods :: CIConstraints t => CiM t GoodStateIdSet
getRemainingGoods = do
  goodStates <- pure . IntSet.fromList . map gsId . Set.toList =<< getGoodStates
  getRootsAccepted >>= pure . IntSet.difference goodStates

buildCurrentResult :: CIConstraints t => CiM t (Assertion t)
buildCurrentResult = do
  fc <- getFeatureCache
  pure . aOr . (map $ rootClauseAssertion fc) =<< getRootClauses

splitGoodStates :: CIConstraints t => Assertion t -> [GoodState t] -> Ceili ([GoodState t], [GoodState t])
splitGoodStates assertion states = do
  let resultPairs state = do
        -- Optimistically assume errors accept good states.
        -- If over-optimistic, a future CEX will rule the feature out.
        result <- testState assertion (gsState state) >>= treatErrorsAs assertion True
        pure (state, result)
  evaluations <- sequence $ map resultPairs states
  let (accepted, rejected) = partition snd evaluations
  pure (map fst accepted, map fst rejected)

splitBadStates :: CIConstraints t => Assertion t -> [BadState t] -> Ceili ([BadState t], [BadState t])
splitBadStates assertion states = do
  let resultPairs state = do
        -- Pessimistically assume errors accept bad states.
        -- We cannot optimistically accept features here, as this is the CEX check mechanism.
        result <- testState assertion (bsState state) >>= treatErrorsAs assertion True
        pure (state, result)
  evaluations <- sequence $ map resultPairs states
  let (accepted, rejected) = partition snd evaluations
  pure (map fst accepted, map fst rejected)

treatErrorsAs :: Pretty t => Assertion t -> Bool -> PredicateResult -> Ceili Bool
treatErrorsAs assertion err result = case result of
  Accepted  -> pure True
  Rejected  -> pure False
  Error msg -> (log_e $ "SMT error: " ++ msg ++ ", assertion: " ++ (show . pretty $ assertion)) >> pure err

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
