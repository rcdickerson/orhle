{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.RelationalPTS
  ( RelSpecImpPTSContext(..)
  , relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import qualified Ceili.FeatureLearning.LinearInequalities as LI
--import qualified Ceili.InvariantInference.LoopInvGen as Lig
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp ( IterStateMap )
import Ceili.Name
import Ceili.ProgState
import Ceili.StatePredicate
import Control.Monad.Trans ( lift )
import Data.Maybe ( catMaybes )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.UUID
import qualified Orhle.CInvGen as CI
--import qualified Orhle.DTLearn2 as DTL
import Orhle.SpecImp
import Orhle.StepStrategy
import Prettyprinter
import System.Random ( randomRIO )

data RelSpecImpPTSContext t e = RelSpecImpPTSContext { rsipc_specEnv          :: SpecImpEnv t e
                                                     , rsipc_loopHeadStates   :: LoopHeadStates t
                                                     , rsipc_programNames     :: Set Name
                                                     , rsipc_programLits      :: Set t
                                                     }

toSinglePTSContext :: SpecImpQuant -> RelSpecImpPTSContext t e -> SpecImpPTSContext t e
toSinglePTSContext quant (RelSpecImpPTSContext specEnv headStates names lits) =
  SpecImpPTSContext quant specEnv headStates names lits

combineLoopHeadStates :: Ord t => RelSpecImpPTSContext t e -> [UUID] -> [ProgState t]
combineLoopHeadStates ctx uuids =
  let
    headStates = rsipc_loopHeadStates ctx
    findStateMap uuid = Map.findWithDefault Map.empty uuid headStates
  in concat . (map Set.toList) . Map.elems . combineIterStateMaps $ map findStateMap uuids

combineIterStateMaps :: Ord t => [IterStateMap t] -> IterStateMap t
combineIterStateMaps = Map.unionsWith $ \left right ->
  Set.map (uncurry Map.union) $ Set.cartesianProduct left right

relBackwardPT :: ( Embeddable Integer t
                 , Ord t
                 , AssertionParseable t
                 , ValidCheckable t
                 , Pretty t
                 , StatePredicate (Assertion t) t
                 , SatCheckable t
                 )
              => BackwardStepStrategy t
              -> RelSpecImpPTSContext t (SpecImpProgram t)
              -> [SpecImpProgram t]
              -> [SpecImpProgram t]
              -> Assertion t
              -> Ceili (Assertion t)
relBackwardPT stepStrategy ctx aprogs eprogs post =
  relBackwardPT' stepStrategy ctx (ProgramRelation aprogs eprogs) post


relBackwardPT' :: ( Embeddable Integer t
                  , Ord t
                  , Pretty t
                  , AssertionParseable t
                  , ValidCheckable t
                  , SatCheckable t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> ProgramRelation t
               -> Assertion t
               -> Ceili (Assertion t)
relBackwardPT' stepStrategy ctx (ProgramRelation aprogs eprogs) post = do
  -- log_d   "[RelationalPTS] --------------------------------"
  -- log_d   "[RelationalPTS] Taking step on:"
  -- log_d $ "[RelationalPTS] Post: " ++ (show $ pretty post)
  -- log_d $ "[RelationalPTS] Universal programs:"
  -- log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) aprogs) <> hardline
  -- log_d $ "[RelationalPTS] Existential programs:"
  -- log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) eprogs) <> hardline
  Step selection aprogs' eprogs' <- stepStrategy aprogs eprogs
  -- log_d $ "[RelationalPTS] Step: " ++ (show $ pretty selection)
  -- log_d   "[RelationalPTS] --------------------------------"
  case selection of
    NoSelectionFound ->
      case (aprogs', eprogs') of
        ([], []) -> return post
        _ -> throwError "Unable to find step"
    UniversalStatement stmt -> do
      post' <- impBackwardPT (toSinglePTSContext SIQ_Universal ctx) stmt post
      relBackwardPT stepStrategy ctx aprogs' eprogs' post'
    ExistentialStatement stmt -> do
      post' <- impBackwardPT (toSinglePTSContext SIQ_Existential ctx) stmt post
      relBackwardPT stepStrategy ctx aprogs' eprogs' post'
    LoopFusion aloops eloops -> do
      let continueWithInv inv = useInvariant inv stepStrategy ctx aloops eloops aprogs' eprogs' post
      let annotatedInvars = Set.toList . Set.fromList . catMaybes $ (map invar aloops) ++ (map invar eloops)
      case annotatedInvars of
        (_:_) -> continueWithInv (And annotatedInvars)
        []    -> do
          mInvariant <- inferInvariant stepStrategy ctx aloops eloops post
          case mInvariant of
            Just inv -> continueWithInv inv
            Nothing -> do
              log_e "[RelationalPTS] Unable to infer loop invariant, proceeding with False"
              continueWithInv AFalse -- TODO: Fall back to single stepping over loops.


useInvariant :: ( Embeddable Integer t
                , Ord t
                , AssertionParseable t
                , ValidCheckable t
                , SatCheckable t
                , Pretty t
                , StatePredicate (Assertion t) t
                )
             => Assertion t
             -> BackwardStepStrategy t
             -> RelSpecImpPTSContext t (SpecImpProgram t)
             -> [ImpWhile t (SpecImpProgram t)]
             -> [ImpWhile t (SpecImpProgram t)]
             -> [SpecImpProgram t]
             -> [SpecImpProgram t]
             -> Assertion t
             -> Ceili (Assertion t)
useInvariant invariant stepStrategy ctx aloops eloops aprogs' eprogs' post = do
  wpInvar <- relBackwardPT stepStrategy ctx (map body aloops) (map body eloops) invariant
  let conds = map condA (aloops ++ eloops)
  isSufficient <- checkValidB $ Imp (And $ invariant:(map Not conds)) post
  isInvariant  <- checkValidB $ Imp (And $ invariant:conds) wpInvar
  -- TODO: Lockstep
  -- TODO: Variant
  case (isSufficient, isInvariant) of
    (True, True) -> do
      relBackwardPT stepStrategy ctx aprogs' eprogs' invariant
    (False, _)   -> do
      log_e "[RelationalPTS] Invariant is insufficient to establish post"
      return AFalse
    (_, False)   -> do
      log_e "[RelationalPTS] Invariant is not invariant on loop body"
      return AFalse


inferInvariant :: ( Embeddable Integer t
                  , Ord t
                  , AssertionParseable t
                  , SatCheckable t
                  , ValidCheckable t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> [ImpWhile t (SpecImpProgram t)]
               -> [ImpWhile t (SpecImpProgram t)]
               -> Assertion t
               -> Ceili (Maybe (Assertion t))
inferInvariant stepStrategy ctx aloops eloops post =
  let
    allLoops = aloops ++ eloops
    bodies = ProgramRelation (map body aloops) (map body eloops)
    conds = map condA allLoops
    -- TODO: Lockstep
    -- TODO: Variant
    headStates = combineLoopHeadStates ctx $ catMaybes $ map (iwm_id . impWhile_meta) allLoops
  in case headStates of
    [] -> throwError "Insufficient test head states for while loop, did you run populateTestStates?"
    _  -> do
      let names = rsipc_programNames ctx
      let lits  = rsipc_programLits ctx
      let lis   = LI.linearInequalities (Set.map embed lits) names
      --let separatorLearner =  Lig.SeparatorLearner DTL.emptyLearnerContext (DTL.learnSeparator 12 2 lis) DTL.resetQueue
      -- let lis = Set.fromList [ Lte (Var $ Name "test!1!counter" 0) (Num $ embed @Integer 5)
      --                        , Lte (Var $ Name "test!2!counter" 0) (Num $ embed @Integer 5)
      --                        , Gte (Var $ Name "test!1!lastTime" 0) (Num $ embed @Integer 0)
      --                        , Gte (Var $ Name "test!2!lastTime" 0) (Num $ embed @Integer 0)
      --                        , Eq (Sub [Var $ Name "test!1!currentTime" 0, Var $ Name "test!1!lastTime" 0]) (Num $ embed @Integer 100)
      --                        , Eq (Sub [Var $ Name "test!2!currentTime" 0, Var $ Name "test!2!lastTime" 0]) (Num $ embed @Integer 101)
      --                        , Eq (Var $ Name "test!1!currentTotal" 0) (Mul [Num $ embed @Integer 100, (Var $ Name "test!1!counter" 0)])
      --                        , Eq (Var $ Name "test!2!currentTotal" 0) (Mul [Num $ embed @Integer 101, (Var $ Name "test!2!counter" 0)])
      --                        ]
      -- result <- Lig.loopInvGen ctx
      --                          (relBackwardPT' stepStrategy)
      --                          conds
      --                          bodies
      --                          post
      --                          headStates
      --                          separatorLearner
      --DTI.dtInvGen ctx 2 12 (relBackwardPT' stepStrategy) conds bodies post headStates lis
      someHeadStates <- lift . lift $ randomSample 15 headStates
      let ciConfig = CI.Configuration 2 12 lis (relBackwardPT' stepStrategy) ctx
      let ciJob    = CI.Job Set.empty (Set.fromList $ someHeadStates) (aAnd conds) bodies post
      CI.cInvGen ciConfig ciJob

body :: ImpWhile t e -> e
body (ImpWhile _ b _) = b

condA :: ImpWhile t e -> Assertion t
condA (ImpWhile c _ _) = bexpToAssertion c

invar :: ImpWhile t e -> Maybe (Assertion t)
invar (ImpWhile _ _ meta) = iwm_invariant meta

-- Adapted from https://www.programming-idioms.org/idiom/158/random-sublist/2123/haskell
randomSample :: Int -> [a] -> IO [a]
randomSample 0 _ = pure []
randomSample k x | k >= length x = pure x
randomSample k x = do
   i <- randomRIO (0, length x - 1)
   let (a, e:b) = splitAt i x
   l <- randomSample (k-1) (a ++ b)
   pure (e : l)

---------------------------
-- Relational "Programs" --
---------------------------

data ProgramRelation t = ProgramRelation { rp_aprogs :: [SpecImpProgram t]
                                         , rp_eprogs :: [SpecImpProgram t]
                                         } deriving Show

instance CollectableNames (ProgramRelation t) where
  namesIn (ProgramRelation aprogs eprogs) = Set.union (namesIn aprogs) (namesIn eprogs)
