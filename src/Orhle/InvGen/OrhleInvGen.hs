{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}

module Orhle.InvGen.OrhleInvGen
  ( Configuration(..)
  , Job(..)
  , orhleInvGen
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
import Ceili.PTS ( BackwardPT )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.State ( StateT, evalStateT, get, put )
import Data.Either ( partitionEithers )
import qualified Data.IntSet as IntSet
import Data.List ( partition )
import Data.Set ( Set )
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe ( catMaybes )
import Orhle.InvGen.Clause
import Orhle.InvGen.Feature
import Orhle.InvGen.SearchQueue
import Orhle.InvGen.State
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
  { jobBadStates          :: [ProgState t]
  , jobConcreteGoodStates :: [ProgState t]
  , jobAbstractGoodStates :: [ProgState t]
  , jobLoopConds          :: [Assertion t]
  , jobPost               :: Assertion t
  }


----------------------
-- Type Constraints --
----------------------

type OigConstraints t = ( AssertionParseable t
                        , Embeddable Integer t
                        , Ord t
                        , Pretty t
                        , SMT.SatCheckable t
                        , SMT.ValidCheckable t
                        , StatePredicate (Assertion t) t
                        )


------------
-- Search --
------------

data Search t = Search
  { searchFoundClauses :: [Clause t]
  , searchGoalQuery    :: Assertion t -> Assertion t
  , searchQueue        :: Queue t
  }


-----------------------------
-- Computation Environment --
-----------------------------

data OigEnv t = OigEnv { envCurrentSearch     :: Search t
                       , envFeatureCache      :: FeatureCache t
                       , envFeatureCandidates :: [Assertion t]
                       , envLoopConds         :: [Assertion t]
                       , envMaxClauseSize     :: Int
                       , envStates            :: States t
                       }

mkOigEnv :: OigConstraints t
         => Configuration c p t
         -> Job p t
         -> OigEnv t
mkOigEnv config job =
  let
    states     = mkClosedStates (jobBadStates job) (jobConcreteGoodStates job) (jobAbstractGoodStates job)
    candidates = Set.toList $ (cfgFeatureGenerator config) (cfgMaxFeatureSize config)
  in OigEnv { envCurrentSearch     = Search [] (\_ -> ATrue) (qEmpty sfBreadthFirst)
            , envFeatureCache      = fcEmpty
            , envFeatureCandidates = candidates
            , envLoopConds         = jobLoopConds job
            , envMaxClauseSize     = cfgMaxClauseSize config
            , envStates            = states
            }


-----------------------
-- Computation Monad --
-----------------------

type OigM t = StateT (OigEnv t) Ceili

enqueue :: Ord t => Entry t -> OigM t ()
enqueue entry = do
  env <- get
  let search = envCurrentSearch env
  let queue = searchQueue search
  let search' = search { searchQueue = qInsert entry queue }
  put $ env { envCurrentSearch = search' }

dequeue :: Ord t => OigM t (Maybe (Entry t))
dequeue = do
  env <- get
  let search = envCurrentSearch env
  let (mEntry, queue') = qPop $ searchQueue search
  let search' = search { searchQueue = queue' }
  put $ env { envCurrentSearch = search' }
  pure mEntry

addClause :: Clause t -> OigM t ()
addClause clause = do
  env <- get
  let search = envCurrentSearch env
  let clauses' = clause:(searchFoundClauses search)
  let search' = search { searchFoundClauses = clauses' }
  put $ env { envCurrentSearch = search' }

resetSearch :: OigM t ()
resetSearch = do
  env <- get
  let search = envCurrentSearch env
  let scoreFun = qScoreFun $ searchQueue search
  let search' = search { searchFoundClauses = []
                       , searchQueue = qEmpty scoreFun
                       }
  put $ env { envCurrentSearch = search' }


setCurrentSearch :: Search t -> OigM t ()
setCurrentSearch search =
  get >>= (\env -> pure $ env { envCurrentSearch = search }) >>= put

clog_d :: String -> OigM t ()
clog_d = lift . log_d

clog_e :: String -> OigM t ()
clog_e = lift . log_e

clog_i :: String -> OigM t ()
clog_i = lift . log_i


------------------------------------
-- orhleInvGen (Main Entry Point) --
------------------------------------

orhleInvGen :: OigConstraints t
            => Configuration c p t
            -> Job p t
            -> Ceili (Maybe (Assertion t))
orhleInvGen config job = do
  log_i $ "[OrhleInvGen] Beginning invariant inference"
  let env =  mkOigEnv config job
  evalStateT (orhleInvGen' job) env

orhleInvGen' :: OigConstraints t
             => Job p t
             -> OigM t (Maybe (Assertion t))
orhleInvGen' job = do
  setCurrentSearch $ Search { searchFoundClauses = []
                            , searchGoalQuery    = \candidate -> aImp candidate (jobPost job)
                            , searchQueue        = qEmpty sfBreadthFirst
                            }
  mCandidate <- fPreGen
  case mCandidate of
    Nothing -> do
      clog_i "[OrhleInvGen] Unable to infer initial invariant candidate."
      pure Nothing
    Just result -> do
      let candidate = vpgAssertion result
      clog_d $ "[CInvGen] Initial candidate, may not be invariant: " ++ (show . pretty $ candidate)
      -- TODO: Strengthen.
      pure . Just $ candidate


-------------
-- vPreGen --
-------------

data VPreGenResult t = VPreGenResult
  { vpgAssertion :: Assertion t
  , vpgClauses   :: [Clause t]
  }

vpgTrue :: VPreGenResult t
vpgTrue = VPreGenResult ATrue []

vpgFalse :: VPreGenResult t
vpgFalse = VPreGenResult AFalse []

fPreGen :: OigConstraints t => OigM t (Maybe (VPreGenResult t))
fPreGen = do
  badStates     <- get >>= pure . stBadStates          . envStates
  conGoodStates <- get >>= pure . stConcreteGoodStates . envStates
  absGoodStates <- get >>= pure . stAbstractGoodStates . envStates
  clog_d $ "[OrhleInvGen] Starting vPreGen pass"
  clog_d . show $ pretty "[OrhleInvGen]   concrete good states:" <+> pretty (Map.size conGoodStates)
  clog_d . show $ pretty "[OrhleInvGen]   abstract good states:" <+> pretty (Map.size absGoodStates)
  clog_d . show $ pretty "[OrhleInvGen]   bad states: "          <+> pretty (Map.size badStates)

  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> do
      clog_d "[OrhleInvGen] Unable to find separator."
      pure Nothing
    Just result -> do
      query <- get >>= pure . searchGoalQuery . envCurrentSearch
      let candidate = vpgAssertion result
      clog_d . show $ pretty "[OrhleInvGen] Candidate precondition:" <+> (align . pretty) candidate
      mCex <- lift $ findCounterexample (query candidate)
      case mCex of
        FormulaValid -> pure $ Just result
        SMTTimeout   -> throwError "SMT timeout"
        SMTUnknown   -> throwError "SMT returned unknown"
        Counterexample cex -> do
          states <- get >>= pure . envStates
          cexState <- lift $ extractState [] [] cex >>= pure . stCloseNames states
          clog_d . show $ pretty "[OrhleInvGen] Found counterexample:" <+> (align . pretty) cexState
          resetSearch >> addCounterexample cexState >> fPreGen

-- TODO: This is fragile.
extractState :: Pretty t => [Name] -> [Name] -> Assertion t -> Ceili (ProgState t)
extractState freshNames names assertion = case assertion of
  Eq lhs rhs -> pure $ Map.fromList [(extractName lhs, extractInt rhs)]
  And as     -> pure . Map.unions =<< mapM (extractState freshNames names) as
  _          -> error $ "Unexpected assertion: " ++ show assertion
  where
    extractName arith = case arith of
      Var name -> substituteAll freshNames names name
      _ -> error $ "Unexpected arith (expected name): " ++ show arith
    extractInt arith = case arith of
      Num n -> n
      _ -> error $ "Unexpected arith (expected int): " ++ show arith

-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: OigConstraints t => OigM t (Maybe (VPreGenResult t))
learnSeparator = do
  clog_d $ "[CInvGen] Beginning separator search."
  badStates     <- get >>= pure . stBadStates          . envStates
  conGoodStates <- get >>= pure . stConcreteGoodStates . envStates
  absGoodStates <- get >>= pure . stAbstractGoodStates . envStates

  if Map.null badStates
    then do clog_d "[OrhleInvGen] No bad states, returning true."; pure $ Just vpgTrue
  else if Map.null conGoodStates && Map.null absGoodStates
    then do clog_d "[OrhleInvGen] No good states, returning false."; pure $ Just vpgFalse
  else processQueue

processQueue :: OigConstraints t => OigM t (Maybe (VPreGenResult t))
processQueue = do
  mSuccess <- checkSuccess
  case mSuccess of
    Just success -> pure $ Just success
    Nothing -> do
      mEntry <- dequeue
      case mEntry of
        Nothing -> do
          clog_d $ "[OrhleInvGen] Search queue is empty, failing."
          pure Nothing
        Just entry ->
          processEntry entry

processEntry :: OigConstraints t => Entry t -> OigM t (Maybe (VPreGenResult t))
processEntry entry = do
  maxClauseSize <- get >>= pure . envMaxClauseSize
  if IntSet.size (entryCandidate entry) >= maxClauseSize
    then processQueue
    else do
      nextFeatures <- usefulFeatures entry
      mSuccess     <- enqueueNextLevel entry nextFeatures
      case mSuccess of
        Nothing      -> processQueue
        Just success -> pure $ Just success

usefulFeatures :: OigConstraints t => Entry t -> OigM t [Feature t]
usefulFeatures entry = do
  let computeUsefulFeatures useful = do
        fc <- get >>= pure . envFeatureCache
        allBads <- get >>= pure . stBadStateIds . envStates
        alreadyRejectedBads <- get >>= pure
                             . clausesRejectedBads fc
                             . searchFoundClauses
                             . envCurrentSearch
        let remainingBads = IntSet.toList
                          $ allBads `IntSet.difference` alreadyRejectedBads
        pure $ filter useful
             . fcLookupFeatures fc
             . IntSet.toList . IntSet.unions
             $ fcFeaturesWhichReject remainingBads fc
  let filterByCons feature =
        let
          featAccepted      = featAcceptedConGoods feature
          entryAccepted     = entryAcceptedConGoods entry
          remainingAccepted = entryAccepted `IntSet.intersection` featAccepted
        in not $ IntSet.null remainingAccepted
  let filterByAbs feature =
        let
          featAccepted      = featAcceptedAbsGoods feature
          entryAccepted     = entryAcceptedAbsGoods entry
          remainingAccepted = entryAccepted `IntSet.intersection` featAccepted
        in not $ IntSet.null remainingAccepted

  alreadyAcceptedConGoods <- get >>= pure
                           . clausesAcceptedConGoods
                           . searchFoundClauses
                           . envCurrentSearch
  if not (entryAcceptedConGoods entry `IntSet.isSubsetOf` alreadyAcceptedConGoods)
    then computeUsefulFeatures filterByCons
    else do
      alreadyAcceptedAbsGoods <- get >>= pure
                               . clausesOptimisticAcceptedAbsGoods
                               . searchFoundClauses
                               . envCurrentSearch
      if not (entryAcceptedAbsGoods entry `IntSet.isSubsetOf` alreadyAcceptedAbsGoods)
        then computeUsefulFeatures filterByAbs
        else pure [] --Entry is not interesting.


enqueueNextLevel :: OigConstraints t => Entry t -> [Feature t] -> OigM t (Maybe (VPreGenResult t))
enqueueNextLevel _ [] = pure Nothing
enqueueNextLevel entry (newFeature:rest) = do
  fc <- get >>= pure . envFeatureCache
  let candidateFeatureIds    = IntSet.toList $ entryCandidate entry
  let newCandidateFeatureIds = (featId newFeature):candidateFeatureIds

  let newCandidateRejected   = IntSet.unions $ map (\fid -> fcRejectedBads fid fc) newCandidateFeatureIds
  allBads <- get >>= pure . stBadStateIds . envStates
  let remainingBads = allBads `IntSet.difference` newCandidateRejected
  let newAcceptedCon = IntSet.intersection (entryAcceptedConGoods entry)
                                           (featAcceptedConGoods  newFeature)
  let newAcceptedAbs = IntSet.intersection (entryAcceptedAbsGoods entry)
                                           (featAcceptedAbsGoods  newFeature)

  if not $ IntSet.null remainingBads
    then do
      enqueue $ Entry { entryCandidate               = IntSet.fromList newCandidateFeatureIds
                      , entryRejectedBads            = newCandidateRejected
                      , entryAcceptedConGoods        = newAcceptedCon
                      , entryAcceptedAbsGoods        = newAcceptedAbs
                      }
      enqueueNextLevel entry rest
    else do
      -- Found a new potential clause. Accepted abstract good states are optimistic,
      -- compute the actual accepted abstract states to be sure.
      let newCandidateFeatures = fcLookupFeatures fc newCandidateFeatureIds
      states <- get >>= pure . envStates
      let maxAcceptedAbs = stLookupAbstractGoodStates states $ IntSet.toList newAcceptedAbs
      actualAcceptedAbs <- computeActualAcceptedAbs newCandidateFeatures maxAcceptedAbs
      if null actualAcceptedAbs
        then enqueueNextLevel entry rest
        else do
          addClause $ Clause { clauseFeatures         = IntSet.fromList newCandidateFeatureIds
                             , clauseAcceptedConGoods = newAcceptedCon
                             , clauseAcceptedAbsGoods = IntSet.fromList . map agsId $ actualAcceptedAbs
                             }
          mSuccess <- checkSuccess
          case mSuccess of
            Nothing      -> enqueueNextLevel entry rest
            Just success -> pure $ Just success

computeActualAcceptedAbs :: OigConstraints t
                         => [Feature t]
                         -> [AbstractGoodState t]
                         -> OigM t [AbstractGoodState t]
computeActualAcceptedAbs features maxAcceptedStates = do
  let assertion = aAnd $ map featAssertion features
  evaluations <- lift $ mapM (testAgs assertion) maxAcceptedStates
  let (accepted, _) = partition snd $ evaluations
  pure $ map fst accepted

checkSuccess :: OigConstraints t => OigM t (Maybe (VPreGenResult t))
checkSuccess = do
  foundClauses <- get >>= pure . searchFoundClauses . envCurrentSearch
  let clauseAcceptedCon = IntSet.unions $ map clauseAcceptedConGoods foundClauses
  let clauseAcceptedAbs = IntSet.unions $ map clauseAcceptedAbsGoods foundClauses

  allCon <- get >>= pure . stConcreteGoodStateIds . envStates
  allAbs <- get >>= pure . stAbstractGoodStateIds . envStates

  let remainingCon = allCon `IntSet.difference` clauseAcceptedCon
  let remainingAbs = allAbs `IntSet.difference` clauseAcceptedAbs

  if IntSet.null remainingCon && IntSet.null remainingAbs
    then do
      fc <- get >>= pure . envFeatureCache
      pure . Just $ VPreGenResult (clausesToAssertion fc foundClauses) foundClauses
    else pure Nothing


---------------------------
-- Counterexample Update --
---------------------------

addCounterexample :: OigConstraints t => ProgState t -> OigM t ()
addCounterexample cex = do
  env <- get
  let (badState, states') = stAddBadState cex (envStates env)
  fc' <- lift $ fcAddBadState (bsId badState) (testFeatureRejects cex) (envFeatureCache env)
  put $ env { envStates       = states'
            , envFeatureCache = fc'
            }
  addNewlyUsefulFeatures   badState
  addNewlyUsefulCandidates badState

testFeatureRejects :: OigConstraints t => ProgState t -> Feature t -> Ceili Bool
testFeatureRejects cex feature = do
  result <- testState (featAssertion feature) cex
  case result of
    Accepted  -> pure False
    Rejected  -> pure True
    Error err -> throwError err

addNewlyUsefulFeatures :: OigConstraints t => BadState t -> OigM t ()
addNewlyUsefulFeatures newBadState = do
  fc <- get >>= pure . envFeatureCache
  let rejectingFeatureIds = IntSet.toList . IntSet.unions
                          $ fcFeaturesWhichReject [bsId newBadState] fc
  let rejectingFeatures   = fcLookupFeatures fc rejectingFeatureIds
  let toFeaturePair feature = (feature, fcRejectedBads (featId feature) fc)
  mapM_ (uncurry seedFeature) (map toFeaturePair rejectingFeatures)

addNewlyUsefulCandidates :: OigConstraints t => BadState t-> OigM t ()
addNewlyUsefulCandidates newBadState = do
  env <- get
  let rejectsNewBad assertion = do
        result <- lift $ testState assertion (bsState newBadState)
        case result of
          Accepted  -> pure $ Left assertion
          Rejected  -> pure $ Right assertion
          Error err -> throwError $ "SMT error evaluating feature candidate: " ++ err
  (candidates', useful) <- pure . partitionEithers =<< mapM rejectsNewBad (envFeatureCandidates env)
  let acceptsSomething feature = (not . IntSet.null . featAcceptedConGoods $ feature)
                              && (not . IntSet.null . featAcceptedAbsGoods $ feature)
  newFeatures <- mapM assertionToFeature useful >>= pure . filter (acceptsSomething . fst) . catMaybes
  let fc' = foldr (uncurry fcAddFeature) (envFeatureCache env) newFeatures
  put $ env { envFeatureCache      = fc'
            , envFeatureCandidates = candidates'
            }
  mapM_ (uncurry seedFeature) newFeatures

assertionToFeature :: OigConstraints t => Assertion t -> OigM t (Maybe (Feature t, BadStateIdSet))
assertionToFeature assertion = do
  conGoodStates <- get >>= pure . Map.elems . stConcreteGoodStates . envStates
  acceptedCons <- lift $ mapM (testCgs assertion) conGoodStates
              >>= pure . map fst . fst . partition snd
  if (not . null $ conGoodStates) && (null acceptedCons)
    then pure Nothing -- No need to do any more work.
    else do
      badStates     <- get >>= pure . Map.elems . stBadStates . envStates
      rejectedBads  <- lift $ mapM (testBs assertion) badStates
                   >>= pure . map fst . fst . partition (not . snd)

      absGoodStates <- get >>= pure . Map.elems . stAbstractGoodStates . envStates
      acceptedAbs   <- lift $ mapM (testAgs assertion) absGoodStates
                    >>= pure . map fst . fst . partition snd

      env <- get
      let (featureId, fc') = fcIncrementId $ envFeatureCache env
      put $ env { envFeatureCache = fc' }

      let feature = Feature { featId               = featureId
                            , featAssertion        = assertion
                            , featAcceptedConGoods = IntSet.fromList . map cgsId $ acceptedCons
                            , featAcceptedAbsGoods = IntSet.fromList . map agsId $ acceptedAbs
                            }
      let rejectedIds = IntSet.fromList . map bsId $ rejectedBads
      pure $ Just (feature, rejectedIds)

seedFeature :: OigConstraints t => Feature t -> BadStateIdSet -> OigM t ()
seedFeature feature rejectedBads = do
  badStateIds <- get >>= pure . stBadStateIds . envStates
  if badStateIds == rejectedBads
    then addClause $ Clause { clauseFeatures         = IntSet.singleton $ featId feature
                            , clauseAcceptedConGoods = featAcceptedConGoods feature
                            , clauseAcceptedAbsGoods = featAcceptedAbsGoods feature
                            }
    else enqueue   $ Entry  { entryCandidate         = IntSet.singleton $ featId feature
                            , entryRejectedBads      = rejectedBads
                            , entryAcceptedConGoods  = featAcceptedConGoods feature
                            , entryAcceptedAbsGoods  = featAcceptedAbsGoods feature
                            }


-------------------
-- State Testing --
-------------------

testBs :: OigConstraints t => Assertion t -> BadState t -> Ceili (BadState t, Bool)
testBs assertion state = do
  result <- testState assertion (bsState state)
  case result of
    Accepted  -> pure (state, True)
    Rejected  -> pure (state, False)
    Error err -> throwError err

testCgs :: OigConstraints t => Assertion t -> ConcreteGoodState t -> Ceili (ConcreteGoodState t, Bool)
testCgs assertion state = do
  result <- testState assertion (cgsState state)
  case result of
    Accepted  -> pure (state, True)
    Rejected  -> pure (state, False)
    Error err -> throwError err

testAgs :: OigConstraints t => Assertion t -> AbstractGoodState t -> Ceili (AbstractGoodState t, Bool)
testAgs assertion state = do
  result <- testState assertion (agsState state)
  case result of
    Accepted  -> pure (state, True)
    Rejected  -> pure (state, False)
    Error err -> throwError err
