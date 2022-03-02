{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Orhle.CVInvGen
  ( FeatureGen(..)
  , Job(..)
  , WeakestPre(..)
  , cvInvGen

  -- Exposed for testing.
  , CviEnv(..)
  , CviM
  , Entry(..)
  , Queue
  , closeNames
  , learnSeparator
  , mkCviEnv
  , qInsert
  , qPop
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import Ceili.PTS ( BackwardPT )
import qualified Ceili.SMT as SMT
import Ceili.StatePredicate
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
                         } deriving (Ord, Show)

instance Eq t => Eq (Feature t)
  where f1 == f2 = (featAssertion f1) == (featAssertion f2)


-------------
-- Clauses --
-------------

type Clause t = [Feature t]

emptyClause :: Clause t
emptyClause = []


------------
-- Queues --
------------

data Entry t = Entry { qe_clauses         :: [Clause t]
                     , qe_candidate       :: Clause t
                     } deriving (Eq, Ord, Show)
type Queue t = Map Int (Set (Entry t))

qSize :: Queue t -> Int
qSize = Map.foldr (\set count -> count + Set.size set) 0

qInsert :: Ord t => Entry t -> Queue t -> Queue t
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

entryScore :: Entry t -> Int
entryScore (Entry clauses candidate) = error "unimplemented"


-----------------
-- Computation --
-----------------

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

putQueue :: (Queue t) -> CviM t ()
putQueue queue = do
  CviEnv _ bads goods features fCandidates goalQ names <- get
  put $ CviEnv queue bads goods features fCandidates goalQ names

enqueue :: Ord t => Entry t -> CviM t ()
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
    Nothing -> do clog_d $ "[CVInvGen] Search queue is empty, failing."; pure Nothing
    Just entry -> do
      error "unimplemented"


---------------------------
-- Counterexample Update --
---------------------------

addBadState :: CviConstraints t => ProgState t -> CviM t ()
addBadState badState = error "unimplemented"


-------------
-- Utility --
-------------

closeNames :: CviConstraints t => [Name] -> ProgState t -> ProgState t
closeNames names state =
  let
    ensureIn name st = if Map.member name st
                       then st
                       else Map.insert name (embed (0 :: Integer)) st
  in foldr ensureIn state names


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
