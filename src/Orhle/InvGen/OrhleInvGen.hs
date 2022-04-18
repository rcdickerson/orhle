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
import Control.Arrow ( (>>>) )
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

data Configuration t = Configuration
  { cfgMaxFeatureSize   :: Int
  , cfgMaxClauseSize    :: Int
  , cfgFeatureGenerator :: Int -> Set (Assertion t)
  , cfgWpTransform      :: Assertion t -> Ceili (Assertion t)
  }


----------
-- Jobs --
----------

data Job t = Job
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
                       , envWpTransform       :: Assertion t -> Ceili (Assertion t)
                       }

mkOigEnv :: OigConstraints t
         => Configuration t
         -> Job t
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
            , envWpTransform       = cfgWpTransform config
            }


-----------------------
-- Computation Monad --
-----------------------

type OigM t = StateT (OigEnv t) Ceili

getEnv :: (OigEnv t -> a) -> OigM t a
getEnv getter = get >>= (getter >>> pure)

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
  let clauses' = addClauseRemovingCovered (searchFoundClauses search) clause
  let search' = search { searchFoundClauses = clauses' }
  put $ env { envCurrentSearch = search' }

resetSearch :: OigM t ()
resetSearch = do
  env <- get
  let search   = envCurrentSearch env
  let scoreFun = qScoreFun $ searchQueue search
  let search'  = search { searchFoundClauses = []
                        , searchQueue = qEmpty scoreFun
                        }
  put $ env { envCurrentSearch = search' }

setCurrentSearch :: Search t -> OigM t ()
setCurrentSearch search =
  get >>= (\env -> pure $ env { envCurrentSearch = search }) >>= put

setGoal :: (Assertion t -> Assertion t) -> OigM t ()
setGoal goal = do
  search <- getEnv envCurrentSearch
  let search' = search { searchGoalQuery = goal }
  get >>= (\env -> pure $ env { envCurrentSearch = search' }) >>= put

clog_d :: String -> OigM t ()
clog_d = lift . log_d

clog_i :: String -> OigM t ()
clog_i = lift . log_i


------------------------------------
-- orhleInvGen (Main Entry Point) --
------------------------------------

orhleInvGen :: OigConstraints t
            => Configuration t
            -> Job t
            -> Ceili (Maybe (Assertion t))
orhleInvGen config job = do
  log_i $ "[OrhleInvGen] Beginning invariant inference"
  let env =  mkOigEnv config job
  evalStateT (orhleInvGen' $ jobPost job) env

orhleInvGen' :: OigConstraints t => Assertion t -> OigM t (Maybe (Assertion t))
orhleInvGen' post = do
  nconds <- pure . map Not =<< getEnv envLoopConds
  setGoal $ \assertion -> aImp (aAnd $ assertion:nconds) post
  mCandidate <- fPreGen
  case mCandidate of
    Just result -> strengthen $ vpgAssertion result
    Nothing -> do
      clog_i "[OrhleInvGen] Unable to infer initial invariant candidate." >> printFc
      pure Nothing

strengthen :: OigConstraints t => Assertion t -> OigM t (Maybe (Assertion t))
strengthen candidate = do
  conds       <- getEnv envLoopConds
  wpTransform <- getEnv envWpTransform
  wpInvar     <- lift $ wpTransform candidate
  let invariance assertion = Imp (aAnd $ assertion:conds) wpInvar
  invCex <- lift . findCounterexample . invariance $ candidate
  case invCex of
    FormulaValid -> pure $ Just candidate
    SMTTimeout -> throwError "SMT timeout"
    SMTUnknown -> throwError "SMT returned unknown"
    Counterexample cex -> do
      states <- getEnv envStates
      cexState <- lift $ extractState [] [] cex >>= pure . stCloseNames states
      clog_d . show $ pretty "[OrhleInvGen] Invariance counterexample:" <+> (align . pretty) cexState
      resetSearch >> addCounterexample cexState >> seedRemainingGoods
      clog_d $ "[OrhleInvGen] Strengthening: " ++ (show . pretty $ candidate)
      setGoal invariance
      mStrengthener <- fPreGen
      case mStrengthener of
        Just strengthener -> strengthen $ aAnd [candidate, vpgAssertion strengthener]
        Nothing -> do
          clog_i $ "[OrhleInvGen] Unable to strengthen candidate to be inductive: "
                ++ (show . pretty $ candidate)
          printFc
          pure Nothing

printFc :: Pretty t => OigM t ()
printFc = do
  fc <- getEnv envFeatureCache
  let features = Map.toList $ fcFeaturesById fc
  let rejected = fcRejectedByFeature fc
  let printFeature (fid, feat) = do
        let rej = case Map.lookup fid rejected of
              Nothing  -> pretty "[]"
              Just set -> pretty . IntSet.toList $ set
        clog_d . show $ pretty "(" <> pretty fid <> pretty "," <+>
          pretty feat <> pretty "," <+>
          (pretty . IntSet.toList . featAcceptedConGoods $ feat) <> pretty "," <+>
          (pretty . IntSet.toList . featAcceptedAbsGoods $ feat) <> pretty "," <+>
          rej <> pretty ")"
  mapM_ printFeature features


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
  badStates     <- getEnv $ envStates >>> stBadStates
  conGoodStates <- getEnv $ envStates >>> stConcreteGoodStates
  absGoodStates <- getEnv $ envStates >>> stAbstractGoodStates
  queue         <- getEnv $ envCurrentSearch >>> searchQueue
  clauses       <- getEnv $ envCurrentSearch >>> searchFoundClauses
  clog_d $ "[OrhleInvGen] Starting vPreGen pass"
  clog_d . show $ pretty "[OrhleInvGen]   concrete good states:" <+> pretty (Map.size conGoodStates)
  clog_d . show $ pretty "[OrhleInvGen]   abstract good states:" <+> pretty (Map.size absGoodStates)
  clog_d . show $ pretty "[OrhleInvGen]   bad states:"           <+> pretty (Map.size badStates)
  clog_d . show $ pretty "[OrhleInvGen]   queue size:"           <+> pretty (qSize queue)
  clog_d . show $ pretty "[OrhleInvGen]   clauses:"              <+> pretty (length clauses)

  mSeparator <- learnSeparator
  case mSeparator of
    Nothing -> do
      clog_d "[OrhleInvGen] Unable to find separator."
      pure Nothing
    Just result -> do
      query <- getEnv $ envCurrentSearch >>> searchGoalQuery
      let candidate = vpgAssertion result
      clog_d . show $ pretty "[OrhleInvGen] Candidate precondition:" <+> (align . pretty) candidate
      mCex <- lift $ findCounterexample (query candidate)
      case mCex of
        FormulaValid -> pure $ Just result
        SMTTimeout   -> throwError "SMT timeout"
        SMTUnknown   -> throwError "SMT returned unknown"
        Counterexample cex -> do
          states <- getEnv envStates
          cexState <- lift $ extractState [] [] cex >>= pure . stCloseNames states
          clog_d . show $ pretty "[OrhleInvGen] Found counterexample:" <+> (align . pretty) cexState
          resetSearch >> addCounterexample cexState >> seedRemainingGoods >> fPreGen

-- TODO: This is fragile.
extractState :: Pretty t => [Name] -> [Name] -> Assertion t -> Ceili (ProgState t)
extractState freshNames names assertion =
  case assertion of
    Eq lhs rhs -> pure $ Map.fromList [(extractName lhs, extractInt rhs)]
    And as     -> pure . Map.unions =<< mapM (extractState freshNames names) as
    _          -> error $ "Unexpected assertion: " ++ show assertion
    where
      extractName arith =
        case arith of
          Var name -> substituteAll freshNames names name
          _        -> error $ "Unexpected arith (expected name): " ++ show arith
      extractInt arith =
        case arith of
          Num n -> n
          _     -> error $ "Unexpected arith (expected int): " ++ show arith


-----------------------
-- Separator Learner --
-----------------------

learnSeparator :: OigConstraints t => OigM t (Maybe (VPreGenResult t))
learnSeparator = do
  clog_d $ "[CInvGen] Beginning separator search."
  badStates     <- getEnv $ envStates >>> stBadStates
  conGoodStates <- getEnv $ envStates >>> stConcreteGoodStates
  absGoodStates <- getEnv $ envStates >>> stAbstractGoodStates

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
  -- clog_d $ "Processing entry: " ++ (show . pretty $ entry)
  maxClauseSize <- getEnv envMaxClauseSize
  if IntSet.size (entryCandidate entry) >= maxClauseSize
    then processQueue
    else do
      nextFeatures <- usefulFeatures entry
      -- clog_d $ "Useful features: " ++ (show . pretty $ nextFeatures)
      mSuccess     <- enqueueNextLevel entry nextFeatures
      case mSuccess of
        Nothing      -> processQueue
        Just success -> pure $ Just success

usefulFeatures :: OigConstraints t => Entry t -> OigM t [Feature t]
usefulFeatures entry = do
  let computeUsefulFeatures useful = do
        fc                  <- getEnv $ envFeatureCache
        allBads             <- getEnv $ envStates >>> stBadStateIds
        alreadyRejectedBads <- getEnv $ envCurrentSearch
                                    >>> searchFoundClauses
                                    >>> clausesRejectedBads fc
                                    >>> IntSet.union (entryRejectedBads entry)
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

  alreadyAcceptedConGoods <- getEnv $ envCurrentSearch
                                  >>> searchFoundClauses
                                  >>> clausesAcceptedConGoods
  if not (entryAcceptedConGoods entry `IntSet.isSubsetOf` alreadyAcceptedConGoods)
    then computeUsefulFeatures filterByCons
    else do
      alreadyAcceptedAbsGoods <- getEnv $ envCurrentSearch
                                      >>> searchFoundClauses
                                      >>> clausesAcceptedAbsGoods
      if not (entryAcceptedAbsGoods entry `IntSet.isSubsetOf` alreadyAcceptedAbsGoods)
        then computeUsefulFeatures filterByAbs
        else pure [] --Entry is not interesting.


enqueueNextLevel :: OigConstraints t => Entry t -> [Feature t] -> OigM t (Maybe (VPreGenResult t))
enqueueNextLevel _ [] = pure Nothing
enqueueNextLevel entry (newFeature:rest) = do
  fc <- getEnv envFeatureCache
  let candidateFeatureIds    = IntSet.toList $ entryCandidate entry
  let newCandidateFeatureIds = (featId newFeature):candidateFeatureIds

  let newCandidateRejected = IntSet.unions $ map (\fid -> fcRejectedBads fid fc) newCandidateFeatureIds
  allBads <- getEnv $ envStates >>> stBadStateIds
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
      states <- getEnv envStates
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

  allCon <- getEnv $ envStates >>> stConcreteGoodStateIds
  allAbs <- getEnv $ envStates >>> stAbstractGoodStateIds

  let remainingCon = allCon `IntSet.difference` clauseAcceptedCon
  let remainingAbs = allAbs `IntSet.difference` clauseAcceptedAbs

  if IntSet.null remainingCon && IntSet.null remainingAbs
    then do
      fc <- getEnv envFeatureCache
      pure . Just $ VPreGenResult (clausesToAssertion fc foundClauses) foundClauses
    else pure Nothing


---------------------------
-- Counterexample Update --
---------------------------

addCounterexample :: OigConstraints t => ProgState t -> OigM t ()
addCounterexample cex = do
  states <- getEnv envStates
  let (badState, states') = stAddBadState cex states
  get >>= \env -> put $ env { envStates = states' }

  fc <- getEnv envFeatureCache
  fc' <- lift $ fcAddBadState (bsId badState) (testFeatureRejects cex) fc
  get >>= \env -> put $ env { envFeatureCache = fc' }

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
  fc <- getEnv envFeatureCache
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
  conGoodStates <- getEnv $ envStates >>> stConcreteGoodStates >>> Map.elems
  acceptedCons <- lift $ mapM (testCgs assertion) conGoodStates
              >>= pure . map fst . fst . partition snd
  if (not . null $ conGoodStates) && (null acceptedCons)
    then pure Nothing -- No need to do any more work.
    else do
      badStates     <- getEnv $ envStates >>> stBadStates >>> Map.elems
      rejectedBads  <- lift $ mapM (testBs assertion) badStates
                   >>= pure . map fst . fst . partition (not . snd)

      absGoodStates <- getEnv $ envStates >>> stAbstractGoodStates >>> Map.elems
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

seedRemainingGoods :: OigConstraints t => OigM t()
seedRemainingGoods = do
  allConGoods <- getEnv $ envStates >>> stConcreteGoodStateIds
  alreadyAcceptedConGoods <- getEnv $ envCurrentSearch
                                  >>> searchFoundClauses
                                  >>> clausesAcceptedConGoods
  let remainingConGoods = allConGoods `IntSet.difference` alreadyAcceptedConGoods

  allAbsGoods <- getEnv $ envStates >>> stAbstractGoodStateIds
  alreadyAcceptedAbsGoods <- getEnv $ envCurrentSearch
                                  >>> searchFoundClauses
                                  >>> clausesAcceptedConGoods
  let remainingAbsGoods = allAbsGoods `IntSet.difference` alreadyAcceptedAbsGoods

  fc <- getEnv envFeatureCache
  let conSets = fcFeaturesWhichAcceptConcrete (IntSet.toList remainingConGoods) fc
      absSets = fcFeaturesWhichAcceptConcrete (IntSet.toList remainingAbsGoods) fc
      seedSet = IntSet.unions $ conSets ++ absSets
  let fLookup fid = (fcLookupFeature fc fid, fcRejectedBads fid fc)
      features    = map fLookup $ IntSet.toList seedSet
  mapM_ (uncurry seedFeature) features

seedFeature :: OigConstraints t => Feature t -> BadStateIdSet -> OigM t ()
seedFeature feature rejectedBads = do
  badStateIds <- getEnv $ envStates >>> stBadStateIds
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
