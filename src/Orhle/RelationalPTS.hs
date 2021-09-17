{-# LANGUAGE FlexibleContexts #-}

module Orhle.RelationalPTS
  ( RelSpecImpPTSContext(..)
  , relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp ( IterStateMap )
import Ceili.Name
import qualified Ceili.InvariantInference.Pie as Pie
import Ceili.ProgState
import Ceili.SMTString
import Ceili.StatePredicate
import Data.Maybe ( catMaybes )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.UUID
import Orhle.SpecImp
import Orhle.StepStrategy
import Prettyprinter

data RelSpecImpPTSContext t e = RelSpecImpPTSContext { rsipc_specEnv        :: SpecImpEnv t e
                                                     , rsipc_loopHeadStates :: LoopHeadStates t
                                                     , rsipc_programNames   :: Set Name
                                                     , rsipc_programLits    :: Set t
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
                 , SMTString t
                 , SMTTypeString t
                 , Pretty t
                 , StatePredicate (Assertion t) t
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
                  , AssertionParseable t
                  , SMTString t
                  , SMTTypeString t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> ProgramRelation t
               -> Assertion t
               -> Ceili (Assertion t)
relBackwardPT' stepStrategy ctx (ProgramRelation aprogs eprogs) post = do
  log_d   "[RelationalPTS] --------------------------------"
  log_d   "[RelationalPTS] Taking step on:"
  log_d $ "[RelationalPTS] Post: " ++ (show $ pretty post)
  log_d $ "[RelationalPTS] Universal programs:"
  log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) aprogs) <> hardline
  log_d $ "[RelationalPTS] Existential programs:"
  log_d $ show $ indent 16 $ vsep (map (\p -> pretty "--------" <> hardline <> pretty p) eprogs) <> hardline
  Step selection aprogs' eprogs' <- stepStrategy aprogs eprogs
  log_d $ "[RelationalPTS] Step: " ++ (show $ pretty selection)
  log_d   "[RelationalPTS] --------------------------------"
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
      let annotatedInvars = Set.toList . Set.fromList . catMaybes $ (map invar aloops) ++ (map invar eloops)
      case annotatedInvars of
        (_:_) -> useAnnotatedInvariant (And annotatedInvars) stepStrategy ctx aloops eloops aprogs' eprogs' post
        []    -> inferInvariant stepStrategy ctx aloops eloops aprogs' eprogs' post


useAnnotatedInvariant :: ( Embeddable Integer t
                         , Ord t
                         , AssertionParseable t
                         , SMTString t
                         , SMTTypeString t
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
useAnnotatedInvariant invariant stepStrategy ctx aloops eloops aprogs' eprogs' post = do
  wpInvar <- relBackwardPT stepStrategy ctx (map body aloops) (map body eloops) invariant
  let conds = map condA (aloops ++ eloops)
  isSufficient <- checkValidB $ Imp (And $ invariant:(map Not conds)) post
  isInvariant  <- checkValidB $ Imp (And $ invariant:conds) wpInvar
  -- TODO: Lockstep
  -- TODO: Variant
  case (isSufficient, isInvariant) of
    (True, True) -> do
      log_d "[RelationalPTS] Annotated loop invariant is sufficient and invariant"
      relBackwardPT stepStrategy ctx aprogs' eprogs' invariant
    (False, _)   -> do
      log_e "[RelationalPTS] Annotated loop invariant insufficient to establish post"
      return AFalse
    (_, False)   -> do
      log_e "[RelationalPTS] Annotated loop invariant is not invariant on loop body"
      return AFalse

inferInvariant :: ( Embeddable Integer t
                  , Ord t
                  , AssertionParseable t
                  , SMTString t
                  , SMTTypeString t
                  , Pretty t
                  , StatePredicate (Assertion t) t
                  )
               => BackwardStepStrategy t
               -> RelSpecImpPTSContext t (SpecImpProgram t)
               -> [ImpWhile t (SpecImpProgram t)]
               -> [ImpWhile t (SpecImpProgram t)]
               -> [SpecImpProgram t]
               -> [SpecImpProgram t]
               -> Assertion t
               -> Ceili (Assertion t)
inferInvariant stepStrategy ctx aloops eloops aprogs' eprogs' post =
  let
    allLoops = aloops ++ eloops
    bodies = ProgramRelation (map body aloops) (map body eloops)
    conds = And $ map condA allLoops
    -- TODO: Lockstep
    -- TODO: Variant
    headStates = combineLoopHeadStates ctx $ catMaybes $ map (iwm_id . impWhile_meta) allLoops
  in case headStates of
    [] -> throwError "Insufficient test head states for while loop, did you run populateTestStates?"
    _  -> do
      let names = rsipc_programNames ctx
      let lits  = rsipc_programLits ctx
      result <- Pie.loopInvGen names lits (relBackwardPT' stepStrategy) ctx conds bodies post headStates
      case result of
        Just inv -> relBackwardPT stepStrategy ctx aprogs' eprogs' inv
        Nothing -> do
          log_e "Unable to infer loop invariant, proceeding with False"
          return AFalse -- TODO: Fall back to single stepping over loops.

body :: ImpWhile t e -> e
body (ImpWhile _ b _) = b

condA :: ImpWhile t e -> Assertion t
condA (ImpWhile c _ _) = bexpToAssertion c

invar :: ImpWhile t e -> Maybe (Assertion t)
invar (ImpWhile _ _ meta) = iwm_invariant meta


---------------------------
-- Relational "Programs" --
---------------------------

data ProgramRelation t = ProgramRelation { rp_aprogs :: [SpecImpProgram t]
                                         , rp_eprogs :: [SpecImpProgram t]
                                         } deriving Show

instance CollectableNames (ProgramRelation t) where
  namesIn (ProgramRelation aprogs eprogs) = Set.union (namesIn aprogs) (namesIn eprogs)
