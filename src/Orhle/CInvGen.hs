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
  , buildCurrentResult
  , closeNames
  , entryScore
  , getRemainingGoods
  , learnSeparator
  , mkCIEnv
  , qInsert
  , qPop
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

data RootClause t = Root (Clause t) [RootClause t]
                  | EmptyRoot

rootClauseAcceptedGoods :: RootClause t -> Set (ProgState t)
rootClauseAcceptedGoods root =
  case root of
    EmptyRoot     -> Set.empty
    Root clause _ -> clauseAcceptedGoods clause

rootClauseAssertion :: RootClause t -> Assertion t
rootClauseAssertion root =
  case root of
    EmptyRoot     -> AFalse
    Root clause _ -> aAnd . map featAssertion . clauseFeatures $ clause


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
  in CIEnv Map.empty closedBads closedGoods [EmptyRoot] Set.empty fCandidates goalQuery names maxClauseSize

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
              mapM_ enqueue =<< nextLevel entry nextFeatures
              learnSeparator'

usefulFeatures :: CIConstraints t => Entry t -> CiM t [Feature t]
usefulFeatures (Entry candidate enRejectedBads enAcceptedGoods) = do
  remainingGoods <- getRemainingGoods
  useful <- case candidate of
    [] ->
      -- The candidate is empty. A useful kickoff to a new clause candidate
      -- is any feature accepting currently unaccepted good states.
      pure $ \feature -> not $ Set.disjoint (featAcceptedGoods feature) remainingGoods
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
               && (not $ Set.disjoint optimisticAccepts remainingGoods)
  getFeatures >>= pure . filter useful . Set.toList

nextLevel :: CIConstraints t => Entry t -> [Feature t] -> CiM t [Entry t]
nextLevel _ [] = pure []
nextLevel entry (newFeature:rest) = error "unimplemented"

---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CIConstraints t => ProgState t -> CiM t ()
addBadState = error "unimplemented"


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
  goodStates  <- getGoodStates
  rootClauses <- getRootClauses
  let rootAccepted = Set.unions $ map rootClauseAcceptedGoods rootClauses
  pure $ Set.difference goodStates rootAccepted

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
