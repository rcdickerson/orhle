{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Orhle.CVInvGen
  ( FeatureGen(..)
  , Job(..)
  , WeakestPre(..)
  , cvInvGen

  -- Exposed for testing.
  , Clause(..)
  , CviEnv(..)
  , CviM
  , Entry(..)
  , Feature(..)
  , Queue
  , UpdateFlag(..)
  , acceptsAllGoods
  , addFeature
  , addNewlyUsefulCandidates
  , assertionToEntry
  , assertionToFeature
  , closeNames
  , emptyClause
  , enqueue
  , entryScore
  , entryToAssertion
  , featureToEntry
  , getFeatures
  , getFeatureCandidates
  , getQueue
  , learnSeparator
  , mkCviEnv
  , nextLevel
  , qInsert
  , qPop
  , updateClause
  , updateFeature
  , updateEntry
  , updateQueue
  , usefulFeatures
  ) where

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


----------------------------
-- Job and Configurations --
----------------------------

data Job p t = Job { jobBadStates  :: Set (ProgState t)
                   , jobGoodStates :: Set (ProgState t)
                   , jobLoopCond   :: Assertion t
                   , jobLoopBody   :: p
                   , jobPostCond   :: Assertion t
                   }

data FeatureGen t = FeatureGen { fgMaxFeatureSize   :: Int
                               , fgMaxClauseSize    :: Int
                               , fgFeatureGenerator :: Int -> Set (Assertion t)
                               }

data WeakestPre c p t = WeakestPre { wpSemantics :: BackwardPT c p t
                                   , wpContext   :: c
                                   }

generateFeatures :: FeatureGen t -> Set (Assertion t)
generateFeatures (FeatureGen maxSize _ gen) = gen maxSize


--------------
-- Features --
--------------

data Feature t = Feature { featAssertion     :: Assertion t
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

data Clause t = Clause { clauseFeatures      :: [Feature t]
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


------------
-- Queues --
------------

data Entry t = Entry { entryClauses         :: [Clause t]
                     , entryCandidate       :: Clause t
                     , entryAcceptsAllGoods :: Bool
                     } deriving (Eq, Ord, Show)

nullEntry :: Entry t -> Bool
nullEntry (Entry clauses candidate _) = and (map nullClause clauses)
                                     && nullClause candidate

instance Pretty t => Pretty (Entry t) where
  pretty (Entry clauses candidate _) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Clauses:" <+> pretty clauses
    , pretty "Candidate:" <+> pretty candidate
    ]

type Queue t = Map Int (Set (Entry t))

qSize :: Queue t -> Int
qSize = Map.foldr (\set count -> count + Set.size set) 0

qInsert :: CviConstraints t => Entry t -> Queue t -> Queue t
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

entryScore :: CviConstraints t => Entry t -> Int
entryScore (Entry _ _ True) = fromIntegral (maxBound :: Int)
entryScore entry@(Entry clauses candidate _) =
  let
    acceptedGoods = Set.size $ entryAcceptedGoods entry
    rejectedBads  = Set.size $ entryRejectedBads entry
    numClauses    = length clauses
    candidateSize = length $ clauseFeatures candidate
  in (100 * acceptedGoods) + rejectedBads - numClauses - candidateSize


-----------------------
-- Computation Monad --
-----------------------

data CviEnv t = CviEnv { envQueue             :: Queue t
                       , envBadStates         :: Set (ProgState t)
                       , envGoodStates        :: Set (ProgState t)
                       , envFeatures          :: Set (Feature t)
                       , envFeatureCandidates :: [Assertion t]
                       , envGoalQuery         :: Assertion t -> Ceili (Assertion t)
                       , envStateNames        :: [Name]
                       , envMaxClauseSize     :: Int
                       }
type CviM t = StateT (CviEnv t) Ceili

mkCviEnv :: CviConstraints t => Job p t -> WeakestPre c p t -> [Assertion t] -> Int -> CviEnv t
mkCviEnv (Job badStates goodStates loopCond loopBody postCond) wp fCandidates maxClauseSize =
  let
    nameList            = Set.unions . (map namesIn) . Set.toList
    names               = Set.toList $ Set.union (nameList badStates) (nameList goodStates)
    closedBads          = Set.map (closeNames names) badStates
    closedGoods         = Set.map (closeNames names) goodStates
    negLoopCond         = Not loopCond
    goalQuery candidate = do
      weakestPre <- (wpSemantics wp) (wpContext wp) loopBody candidate
      pure $ aAnd [ Imp (aAnd [candidate, negLoopCond]) postCond -- Establishes Post
                  , Imp (aAnd [candidate, loopCond]) weakestPre  -- Inductive
                  ]
  in CviEnv Map.empty closedBads closedGoods Set.empty fCandidates goalQuery names maxClauseSize

getQueue :: CviM t (Queue t)
getQueue = get >>= pure . envQueue

getBadStates :: CviM t (Set (ProgState t))
getBadStates = get >>= pure . envBadStates

getGoodStates :: CviM t (Set (ProgState t))
getGoodStates = get >>= pure . envGoodStates

getFeatures :: CviM t (Set (Feature t))
getFeatures = get >>= pure . envFeatures

getFeatureCandidates :: CviM t [Assertion t]
getFeatureCandidates = get >>= pure . envFeatureCandidates

getMaxClauseSize :: CviM t Int
getMaxClauseSize = get >>= pure . envMaxClauseSize

addFeature :: Ord t => Feature t -> CviM t ()
addFeature feature = do
  CviEnv queue bads goods features fCandidates goalQ names mcs <- get
  put $ CviEnv queue bads goods (Set.insert feature features) fCandidates goalQ names mcs

putQueue :: Queue t -> CviM t ()
putQueue queue = do
  CviEnv _ bads goods features fCandidates goalQ names mcs <- get
  put $ CviEnv queue bads goods features fCandidates goalQ names mcs

putBadStates :: Set (ProgState t) -> CviM t ()
putBadStates badStates = do
  CviEnv queue _ goods features fCandidates goalQ names mcs <- get
  put $ CviEnv queue badStates goods features fCandidates goalQ names mcs

putFeatures :: Set (Feature t) -> CviM t ()
putFeatures features = do
  CviEnv queue bads goods _ fCandidates goalQ names mcs <- get
  put $ CviEnv queue bads goods features fCandidates goalQ names mcs

putFeatureCandidates :: [Assertion t] -> CviM t ()
putFeatureCandidates fCandidates = do
  CviEnv queue bads goods features _ goalQ names mcs <- get
  put $ CviEnv queue bads goods features fCandidates goalQ names mcs

enqueue :: CviConstraints t => Entry t -> CviM t ()
enqueue entry = do
  queue <- getQueue
  putQueue $ qInsert entry queue

dequeue :: CviM t (Maybe (Entry t))
dequeue = do
  queue <- getQueue
  let (elt, queue') = qPop queue
  putQueue queue'
  pure elt

data GoalStatus t = GoalMet
                  | GoalCex (ProgState t)
                  | SMTError String

checkGoal :: CviConstraints t => Assertion t -> CviM t (GoalStatus t)
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

clog_d :: String -> CviM t ()
clog_d = lift . log_d

clog_e :: String -> CviM t ()
clog_e = lift . log_e


----------------------
-- Type Constraints --
----------------------

type CviConstraints t = ( AssertionParseable t
                        , Embeddable Integer t
                        , Ord t
                        , Pretty t
                        , SMT.SatCheckable t
                        , SMT.ValidCheckable t
                        , StatePredicate (Assertion t) t
                        )


---------------------------------
-- CVInvGen (Main Entry Point) --
---------------------------------

cvInvGen :: CviConstraints t
         => FeatureGen t
         -> WeakestPre c p t
         -> Job p t
         -> Ceili (Maybe (Assertion t))
cvInvGen featureGen wpts job = do
  log_i $ "[CVInvGen] Beginning invariant inference"
  let featureCandidates = Set.toList $ generateFeatures featureGen
  log_d $ "[CVInvGen] " ++ (show $ length featureCandidates) ++ " initial feature candidates."
  let env = mkCviEnv job wpts featureCandidates (fgMaxClauseSize featureGen)
  evalStateT cvInvGen' env

cvInvGen' :: CviConstraints t => CviM t (Maybe (Assertion t))
cvInvGen' = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  clog_d $ "[CVInvGen] Starting vPreGen pass"
  clog_d . show $ pretty "[CVInvGen]   good states:" <+> pretty (Set.size goodStates)
  clog_d . show $ pretty "[CVInvGen]   bad states: " <+> pretty (Set.size badStates)
  -- Try to learn a separator. If we find one, check to see if it meets the goal criteria.
  -- If it does, return it. Otherwise, add the new counterexample and recurse.
  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> clog_d "[CVInvGen] Unable to find separator." >> pure Nothing
    Just separator -> do
      clog_d . show $ pretty "[CVInvGen] Candidate precondition:" <+> (align . pretty) separator
      goalStatus <- checkGoal separator
      case goalStatus of
        GoalCex cex -> do
          clog_d . show $ pretty "[CVInvGen] Found counterexample:" <+> (align . pretty) cex
          addBadState cex
          cvInvGen'
        GoalMet -> do
          clog_d . show $ pretty "[CVInvGen] Found invariant:" <+> (align . pretty) separator
          pure $ Just separator
        SMTError msg -> do
          clog_e . show $ pretty "[CVInvGen]" <+> pretty msg
                      <+> pretty "on candidate" <+> (align . pretty) separator
          cvInvGen' -- Continue now that the problematic assertion is out of the queue.


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: CviConstraints t => CviM t (Maybe (Assertion t))
learnSeparator = do
  queue      <- getQueue
  goodStates <- getGoodStates
  badStates  <- getBadStates
  clog_d $ "[CVInvGen] Beginning separator search. Queue size: " ++ (show $ qSize queue)
  -- Short circuit on trivial separation cases.
  if Set.null badStates
    then do clog_d "[CVInvGen] No bad states, returning true."; pure $ Just ATrue
  else if Set.null goodStates
    then do clog_d "[CVInvGen] No good states, returning false."; pure $ Just AFalse
  else learnSeparator'

learnSeparator' :: CviConstraints t => CviM t (Maybe (Assertion t))
learnSeparator' = do
  mEntry <- dequeue
  case mEntry of
    Nothing -> do
      clog_d $ "[CVInvGen] Search queue is empty, failing."
      pure Nothing
    Just entry -> do
      maxClauseSize <- getMaxClauseSize
      if entryAcceptsAllGoods entry
        then pure . Just $ entryToAssertion entry
      else if clauseSize (entryCandidate entry) >= maxClauseSize
        then learnSeparator'
      else do
          nextFeatures <- usefulFeatures entry
          mapM_ enqueue =<< nextLevel entry nextFeatures
          learnSeparator'

usefulFeatures :: CviConstraints t => Entry t -> CviM t [Feature t]
usefulFeatures entry = do
  features <- pure . Set.toList =<< getFeatures
  case entryCandidate entry of
    candidate | nullClause candidate -> do
      -- The candidate is empty. A useful kickoff to a new clause candidate
      -- is any feature accepting currently unaccepted good states.
      goodStates <- getGoodStates
      let acceptedGoods  = Set.unions $ map clauseAcceptedGoods (entryClauses entry)
      let remainingGoods = Set.difference goodStates acceptedGoods
      let useful feature = not $ Set.disjoint (featAcceptedGoods feature) remainingGoods
      pure $ filter useful features
    candidate | otherwise -> do
      -- A useful addition to an existing candidate rejects something new
      -- while not bringing the accepted states for the new candidate
      -- down to either 1) the empty set or 2) a subset of of the good
      -- states already accepted by the entry's clauses. (Note the former
      -- condition is not a subcase of the latter since the clause list may
      -- be empty.)
      badStates <- getBadStates
      let candAcceptedGoods = clauseAcceptedGoods candidate
      let candRejectedBads  = clauseRejectedBads  candidate
      let candRemainingBads = Set.difference badStates candRejectedBads
      let claAcceptedGoods  = Set.unions $ map clauseAcceptedGoods (entryClauses entry)
      let useful feature =
            let optimisticAccepts = Set.intersection (featAcceptedGoods feature) candAcceptedGoods
            in (not $ Set.disjoint (featRejectedBads feature)  candRemainingBads)
            && (not $ Set.disjoint (featAcceptedGoods feature) candAcceptedGoods)
            && (not $ Set.isSubsetOf optimisticAccepts claAcceptedGoods)
      pure $ filter useful features

nextLevel :: CviConstraints t => Entry t -> [Feature t] -> CviM t [Entry t]
nextLevel _ [] = pure []
nextLevel entry (newFeature:rest) = do
  let minInteresting = Set.unions $ map clauseAcceptedGoods (entryClauses entry)
  mCandidate' <- addFeatureToClause minInteresting newFeature (entryCandidate entry)
  case mCandidate' of
    Nothing ->
      -- Combination turned out not to be feasible; continue.
      nextLevel entry rest
    Just candidate' -> do
      let rejectedBads = clauseRejectedBads candidate'
      badStates <- getBadStates
      let remainingBads = Set.difference badStates rejectedBads
      if Set.null remainingBads
        then do
          -- Found a new clause.
          let clauses' = candidate':(entryClauses entry)
          newEntry <- pure . Entry clauses' candidate' =<< acceptsAllGoods clauses'
          pure . (newEntry:) =<< nextLevel entry rest
        else do
          -- Still have remaining bad states to eliminate before the clause is complete.
          let newEntry = Entry (entryClauses entry) candidate' False
          pure . (newEntry:) =<< nextLevel entry rest

addFeatureToClause :: CviConstraints t
                   => Set (ProgState t)
                   -> Feature t
                   -> Clause t
                   -> CviM t (Maybe (Clause t))
addFeatureToClause minInteresting feature (Clause cFeatures _) = do
  goodStates <- getGoodStates
  let combinedFeatures = feature:cFeatures
  let cfAssertion = aAnd $ map featAssertion combinedFeatures
  (acceptedGoodsList, _) <- lift $ splitStates cfAssertion $ Set.toList goodStates
  case acceptedGoodsList of
    [] -> pure Nothing
    _  -> do
      let acceptedGoods = Set.fromList acceptedGoodsList
      if Set.isSubsetOf acceptedGoods minInteresting
        then pure Nothing
        else pure . Just $ Clause combinedFeatures acceptedGoods

---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CviConstraints t => ProgState t -> CviM t ()
addBadState badState = do
  getQueue     >>= lift . (updateQueue    badState) >>= putQueue
  getFeatures  >>= lift . (updateFeatures badState) >>= putFeatures
  getBadStates >>= pure . (Set.insert     badState) >>= putBadStates
  addNewlyUsefulFeatures   badState
  addNewlyUsefulCandidates badState

updateFeatures :: CviConstraints t => ProgState t -> Set (Feature t) -> Ceili (Set (Feature t))
updateFeatures newBadState features = do
  features' <- mapM (updateFeature newBadState) $ Set.toList features
  pure . Set.fromList . (map fst) $ features'

addNewlyUsefulFeatures :: CviConstraints t => ProgState t -> CviM t ()
addNewlyUsefulFeatures newBadState = do
  features <- getFeatures
  let featuresList = Set.toList features
  let newlyUseful = filter (\f -> Set.member newBadState $ featRejectedBads f) featuresList
  newEntries <- mapM featureToEntry newlyUseful
  mapM_ enqueue newEntries

addNewlyUsefulCandidates :: CviConstraints t => ProgState t -> CviM t ()
addNewlyUsefulCandidates newBadState = do
  featureCandidates <- getFeatureCandidates
  let rejectsNewBad assertion = do
        result <- lift $ testState assertion newBadState
        pure $ if result then Left assertion else Right assertion
  (candidates', newlyUseful) <- pure . partitionEithers =<< mapM rejectsNewBad featureCandidates
  maybeUseful <- mapM assertionToFeature newlyUseful
  let newFeatures = filter (not . Set.null . featAcceptedGoods) maybeUseful
  newEntries <- mapM featureToEntry newFeatures

  putFeatureCandidates candidates'
  mapM_ addFeature newFeatures
  mapM_ enqueue newEntries

-- Update mechanics.

data UpdateFlag = Accepts
                | Rejects
                deriving (Ord, Eq, Show)

anyRejects :: [UpdateFlag] -> UpdateFlag
anyRejects flags = case flags of
  []           -> Accepts
  Rejects:_    -> Rejects
  Accepts:rest -> anyRejects rest

updateFeature :: CviConstraints t => ProgState t -> Feature t -> Ceili (Feature t, UpdateFlag)
updateFeature newBadState (Feature assertion rejectedBads acceptedGoods) = do
  acceptsNewBad <- testState assertion newBadState
  let (rejectedBads', flag) = if acceptsNewBad
                              then (rejectedBads, Accepts)
                              else (Set.insert newBadState rejectedBads, Rejects)
  pure (Feature assertion rejectedBads' acceptedGoods, flag)

updateClause :: CviConstraints t => ProgState t -> Clause t -> Ceili (Clause t, UpdateFlag)
updateClause newBadState (Clause features acceptedGoods) = do
  updatedFeatures <- mapM (updateFeature newBadState) features
  let (features', flags) = unzip updatedFeatures
  pure (Clause features' acceptedGoods, anyRejects flags)

updateEntry :: CviConstraints t => ProgState t -> Entry t -> Ceili (Entry t, [Clause t])
updateEntry newBadState (Entry clauses candidate finished) = do
  updatedClauses <- mapM (updateClause newBadState) clauses
  let (rejectClauses, acceptClauses) = partition ((== Rejects) . snd) updatedClauses
  (candidate', _) <- updateClause newBadState candidate
  let finished' = if null acceptClauses then finished else False
  pure (Entry (map fst rejectClauses) candidate' finished', map fst acceptClauses)

--checkEntry entry i =
--  if Set.null $ entryAcceptedGoods entry
--  then error $ (show i) ++ "Enqueuing entry with no accepted goods: " ++ (show . pretty $ entry)
--  else entry

updateQueue :: CviConstraints t => ProgState t -> Queue t -> Ceili (Queue t)
updateQueue newBadState queue = do
  let entries = Set.toList . Set.unions . Map.elems $ queue
  updatedEntries <- mapM (updateEntry newBadState) entries
  let enqueueUpdate (entry, removed) newQueue =
        case removed of
          [] -> qInsert entry newQueue
          _  -> let entry' = Entry (entryClauses entry) emptyClause False
                in if nullEntry entry' then newQueue else qInsert entry' newQueue
  let enqueueRemoved removed newQueue =
        let rEntries = map (\r -> (Entry [] r False)) removed
        in foldr qInsert newQueue rEntries
  let process (entry, removedClauses) newQueue = enqueueUpdate (entry, removedClauses)
                                               $ enqueueRemoved removedClauses
                                               $ newQueue
  pure $ foldr process Map.empty updatedEntries


-----------------------
-- Entry Conversions --
-----------------------

assertionToFeature :: CviConstraints t => Assertion t -> CviM t (Feature t)
assertionToFeature assertion = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  (_, rejectedBads)  <- lift $ splitStates assertion $ Set.toList badStates
  (acceptedGoods, _) <- lift $ splitStates assertion $ Set.toList goodStates
  pure $ Feature assertion (Set.fromList rejectedBads) (Set.fromList acceptedGoods)

featureToClause :: CviConstraints t => Feature t -> Clause t
featureToClause feature = Clause [feature] (featAcceptedGoods feature)

featureToEntry :: CviConstraints t => Feature t -> CviM t (Entry t)
featureToEntry feature = do
  badStates <- getBadStates
  let featureClause = featureToClause feature
  if Set.null $ Set.difference badStates (featRejectedBads feature)
    then pure . Entry [featureClause] emptyClause =<< acceptsAllGoods [featureClause]
    else pure $ Entry [] featureClause False

assertionToEntry :: CviConstraints t => Assertion t -> CviM t (Entry t)
assertionToEntry assertion = assertionToFeature assertion >>= featureToEntry

entryToAssertion :: Entry t -> Assertion t
entryToAssertion = aOr . map (aAnd . map featAssertion . clauseFeatures) . entryClauses


-------------
-- Utility --
-------------

clauseRejectedBads :: CviConstraints t => Clause t -> Set (ProgState t)
clauseRejectedBads = Set.unions . (map featRejectedBads) . clauseFeatures

entryAcceptedGoods :: CviConstraints t => Entry t -> Set (ProgState t)
entryAcceptedGoods (Entry clauses candidate _) =
  let
    clauseAccepted = Set.unions $ map clauseAcceptedGoods clauses
    candidateAccepted = clauseAcceptedGoods candidate
  in Set.union clauseAccepted candidateAccepted

entryRejectedBads :: CviConstraints t => Entry t -> Set (ProgState t)
entryRejectedBads (Entry clauses candidate _) =
  let
    clauseRejected = Set.unions $ map clauseRejectedBads clauses
    candidateRejected = Set.unions $ map featRejectedBads $ clauseFeatures candidate
  in Set.union clauseRejected candidateRejected

acceptsAllGoods :: CviConstraints t => [Clause t] -> CviM t Bool
acceptsAllGoods clauses = do
  goodStates <- getGoodStates
  let acceptedGoods = Set.unions $ map clauseAcceptedGoods clauses
  let remainingGoods = Set.difference goodStates acceptedGoods
  pure $ Set.null remainingGoods

closeNames :: CviConstraints t => [Name] -> ProgState t -> ProgState t
closeNames names state =
  let
    ensureIn name st = if Map.member name st
                       then st
                       else Map.insert name (embed (0 :: Integer)) st
  in foldr ensureIn state names

splitStates :: CviConstraints t => Assertion t -> [ProgState t] -> Ceili ([ProgState t], [ProgState t])
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
