{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Orhle.CVInvGen
  ( FeatureGen(..)
  , Job(..)
  , WeakestPre(..)
  , cvInvGen

  -- Exposed for testing.
  , Clause
  , CviEnv(..)
  , CviM
  , Entry(..)
  , Feature(..)
  , Queue
  , UpdateFlag(..)
  , acceptsAllGoods
  , addFeature
  , assertionToEntry
  , assertionToFeature
  , closeNames
  , enqueue
  , entryScore
  , entryToAssertion
  , featureToEntry
  , learnSeparator
  , mkCviEnv
  , nextLevel
  , qInsert
  , qPop
  , updateClause
  , updateFeature
  , updateEntry
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
import Data.List ( partition )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Prettyprinter

import Debug.Trace


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
                         } deriving (Ord, Show)

instance Eq t => Eq (Feature t)
  where f1 == f2 = (featAssertion f1) == (featAssertion f2)

instance Pretty t => Pretty (Feature t) where
  pretty (Feature assertion bads goods) =
    align $ encloseSep lbracket rbracket space
    [ pretty "Assertion:" <+> pretty assertion
    , pretty "Rejected bads:" <+> align (prettyProgStates (Set.toList bads))
    , pretty "AcceptedGoods:" <+> align (prettyProgStates (Set.toList goods))
    ]

-------------
-- Clauses --
-------------

type Clause t = [Feature t]


------------
-- Queues --
------------

data Entry t = Entry { entryClauses         :: [Clause t]
                     , entryCandidate       :: Clause t
                     , entryAcceptsAllGoods :: Bool
                     } deriving (Eq, Ord, Show)

instance Pretty t => Pretty (Entry t) where
  pretty (Entry clauses candidate acceptsAllGoods) =
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
    candidateSize = length candidate
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
                       }
type CviM t = StateT (CviEnv t) Ceili

mkCviEnv :: CviConstraints t => Job p t -> WeakestPre c p t -> [Assertion t] -> CviEnv t
mkCviEnv (Job badStates goodStates loopCond loopBody postCond) wp fCandidates =
  let
    nameList            = Set.unions . (map namesIn) . Set.toList
    names               = Set.toList $ Set.union (nameList badStates) (nameList goodStates)
    closedBads          = Set.map (closeNames names) badStates
    closedGoods         = Set.map (closeNames names) goodStates
    negLoopCond         = Not loopCond
    goalQuery candidate = do
      weakestPre <- (wpSemantics wp) (wpContext wp) loopBody candidate
      pure $ aAnd [ Imp (aAnd [candidate, negLoopCond]) postCond     -- Establishes Post
                  , Not $ Imp (aAnd [candidate, negLoopCond]) AFalse -- Non-trivial
                  , Imp (aAnd [candidate, loopCond]) weakestPre      -- Inductive
                  ]
  in CviEnv Map.empty closedBads closedGoods Set.empty fCandidates goalQuery names

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

addFeature :: Ord t => Feature t -> CviM t ()
addFeature feature = do
  CviEnv queue bads goods features fCandidates goalQ names <- get
  put $ CviEnv queue bads goods (Set.insert feature features) fCandidates goalQ names

putQueue :: (Queue t) -> CviM t ()
putQueue queue = do
  CviEnv _ bads goods features fCandidates goalQ names <- get
  put $ CviEnv queue bads goods features fCandidates goalQ names

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

checkGoal :: CviConstraints t => Assertion t -> CviM t (Either (ProgState t) (Assertion t))
checkGoal candidate = do
  goalQuery <- get >>= pure . envGoalQuery
  mCex <- lift $ goalQuery candidate >>= findCounterexample
  case mCex of
    Nothing  -> pure $ Right candidate
    Just cex -> do
      let cexState = extractState cex
      pure $ Left cexState

clog_d :: String -> CviM t ()
clog_d = lift . log_d


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
  let env = mkCviEnv job wpts featureCandidates
  evalStateT cvInvGen' env

cvInvGen' :: CviConstraints t => CviM t (Maybe (Assertion t))
cvInvGen' = do
  badStates  <- getBadStates
  goodStates <- getGoodStates
  clog_d $ "[CVInvGen] Starting vPreGen pass"
  clog_d . show $ pretty "[CVInvGen]   good states: " <+> pretty (Set.size goodStates)
  clog_d . show $ pretty "[CVInvGen]   bad states: "  <+> pretty (Set.size badStates)
  -- Try to learn a separator. If we find one, check to see if it meets the goal criteria.
  -- If it does, return it. Otherwise, add the new counterexample and recurse.
  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> clog_d "[CVInvGen] Unable to find separator." >> pure Nothing
    Just separator -> do
      clog_d . show $ pretty "[CVInvGen] Candidate precondition: " <+> pretty separator
      checkResult <- checkGoal separator
      case checkResult of
        Right invariant -> do
          clog_d . show $ pretty "[CVInvGen] Found invariant: " <+> pretty invariant
          pure $ Just invariant
        Left cex -> do
          clog_d . show $ pretty "[CVInvGen] Found counterexample: " <+> pretty cex
          addBadState cex
          cvInvGen'


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: CviConstraints t => CviM t (Maybe (Assertion t))
learnSeparator = do
  queue      <- getQueue
  goodStates <- getGoodStates
  badStates  <- getBadStates
  clog_d $ "[CVInvGen] Beginning separator search."
  clog_d $ "  bad states:  " ++ (show $ Set.size badStates)
  clog_d $ "  good states: " ++ (show $ Set.size goodStates)
  clog_d $ "  queue size:  " ++ (show $ qSize queue)
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
      -- traceM . show $ pretty "Entry: " <+> pretty entry
      if entryAcceptsAllGoods entry
        then pure . Just $ entryToAssertion entry
        else do
          nextFeatures <- usefulFeatures entry
          mapM_ enqueue =<< nextLevel entry nextFeatures
          learnSeparator'

usefulFeatures :: CviConstraints t => Entry t -> CviM t [Feature t]
usefulFeatures entry = do
  features <- pure . Set.toList =<< getFeatures
  case entryCandidate entry of
    [] -> do
      -- The candidate is empty. A useful kickoff to a new clause candidate
      -- is any feature accepting currently unaccepted good states.
      goodStates <- getGoodStates
      let acceptedGoods  = Set.unions $ map clauseAcceptedGoods (entryClauses entry)
      let remainingGoods = Set.difference goodStates acceptedGoods
      let useful feature = not $ Set.disjoint (featAcceptedGoods feature) remainingGoods
      pure $ filter useful features
    candidate -> do
      -- A useful addition to an existing candidate rejects something new
      -- while not bringing the accepted states for the new candidate
      -- down to 1) the empty set or 2) a subset of the good states the
      -- clauses already accept. (Note the former condition is not a subcase
      -- of the latter since the clause list may be empty.)
      badStates <- getBadStates
      let candAcceptedGoods = clauseAcceptedGoods candidate
      let candRejectedBads  = clauseRejectedBads  candidate
      let candRemainingBads = Set.difference badStates candRejectedBads
      let claAcceptedGoods  = Set.unions $ map clauseAcceptedGoods (entryClauses entry)
      let useful feature =
               (not $ Set.disjoint   (featRejectedBads feature)  candRemainingBads)
            && (not $ Set.disjoint   (featAcceptedGoods feature) candAcceptedGoods)
            && (not $ Set.isSubsetOf (clauseAcceptedGoods (feature:candidate)) claAcceptedGoods)
      pure $ filter useful features

nextLevel :: CviConstraints t => Entry t -> [Feature t] -> CviM t [Entry t]
nextLevel _ [] = pure []
nextLevel entry (newFeature:rest) = do
  let candidate'   = newFeature:(entryCandidate entry)
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


---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CviConstraints t => ProgState t -> CviM t ()
addBadState badState = do
  error "unimplemented"

data UpdateFlag = Accepts
                | Rejects
                deriving (Ord, Eq, Show)

anyRejects :: [UpdateFlag] -> UpdateFlag
anyRejects flags = case flags of
  [] -> Accepts
  Rejects:_ -> Rejects
  Accepts:rest -> anyRejects rest

updateFeature :: CviConstraints t => ProgState t -> Feature t -> Ceili (Feature t, UpdateFlag)
updateFeature newBadState (Feature assertion rejectedBads acceptedGoods) = do
  acceptsNewBad <- testState assertion newBadState
  let (rejectedBads', flag) = if acceptsNewBad
                              then (rejectedBads, Accepts)
                              else (Set.insert newBadState rejectedBads, Rejects)
  pure $ (Feature assertion rejectedBads' acceptedGoods, flag)

updateClause :: CviConstraints t => ProgState t -> Clause t -> Ceili (Clause t, UpdateFlag)
updateClause newBadState features = do
  updatedFeatures <- mapM (updateFeature newBadState) features
  let (features', flags) = unzip updatedFeatures
  pure $ (features', anyRejects flags)

updateEntry :: CviConstraints t => ProgState t -> Entry t -> Ceili (Entry t, [Clause t])
updateEntry newBadState (Entry clauses candidate acceptsAllGoods) = do
  clauses' <- mapM (updateClause newBadState) clauses
  error "unimplemented"


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

featureToEntry :: CviConstraints t => Feature t -> CviM t (Entry t)
featureToEntry feature = do
  badStates <- getBadStates
  if Set.null $ Set.difference badStates (featRejectedBads feature)
    then pure . Entry [[feature]] [] =<< acceptsAllGoods [[feature]]
    else pure $ Entry [] [feature] False

assertionToEntry :: CviConstraints t => Assertion t -> CviM t (Entry t)
assertionToEntry assertion = assertionToFeature assertion >>= featureToEntry

entryToAssertion :: Entry t -> Assertion t
entryToAssertion = aOr . map (aAnd . map featAssertion) . entryClauses


-------------
-- Utility --
-------------

clauseAcceptedGoods :: CviConstraints t => Clause t -> Set (ProgState t)
clauseAcceptedGoods [] = Set.empty
clauseAcceptedGoods (c:cs) =
  let
    first = featAcceptedGoods c
    rest  = map featAcceptedGoods cs
  in foldl Set.intersection first rest

clauseRejectedBads :: CviConstraints t => Clause t -> Set (ProgState t)
clauseRejectedBads = Set.unions . (map featRejectedBads)

entryAcceptedGoods :: CviConstraints t => Entry t -> Set (ProgState t)
entryAcceptedGoods (Entry clauses candidate _) =
  let
    clauseAccepted = Set.unions $ map clauseAcceptedGoods clauses
    candidateAccepted = Set.unions $ map featAcceptedGoods candidate
  in Set.union clauseAccepted candidateAccepted

entryRejectedBads :: CviConstraints t => Entry t -> Set (ProgState t)
entryRejectedBads (Entry clauses candidate _) =
  let
    clauseRejected = Set.unions $ map clauseRejectedBads clauses
    candidateRejected = Set.unions $ map featRejectedBads candidate
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
