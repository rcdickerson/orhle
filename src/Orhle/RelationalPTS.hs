module Orhle.RelationalPTS
  ( relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Name
import qualified Ceili.InvariantInference.Pie as Pie
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set
import Orhle.SpecImp
import Orhle.StepStrategy
import Prettyprinter


relBackwardPT :: BackwardStepStrategy
              -> SpecImpEnv SpecImpProgram
              -> [SpecImpProgram]
              -> [SpecImpProgram]
              -> Assertion
              -> Ceili Assertion
relBackwardPT stepStrategy env aprogs eprogs post =
  relBackwardPT' stepStrategy env (ProgramRelation aprogs eprogs) post


relBackwardPT' :: BackwardStepStrategy
               -> SpecImpEnv SpecImpProgram
               -> ProgramRelation
               -> Assertion
               -> Ceili Assertion
relBackwardPT' stepStrategy env (ProgramRelation aprogs eprogs) post = do
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
      post' <- impBackwardPT (SIQ_Universal, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    ExistentialStatement stmt -> do
      post' <- impBackwardPT (SIQ_Existential, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    LoopFusion aloops eloops -> do
      let annotatedInvars = Set.toList . Set.fromList . catMaybes $ (map invar aloops) ++ (map invar eloops)
      case annotatedInvars of
        (_:_) -> useAnnotatedInvariant (And annotatedInvars) stepStrategy env aloops eloops aprogs' eprogs' post
        []    -> inferInvariant stepStrategy env aloops eloops aprogs' eprogs' post


useAnnotatedInvariant :: Assertion
                      -> BackwardStepStrategy
                      -> SpecImpEnv SpecImpProgram
                      -> [ImpWhile SpecImpProgram]
                      -> [ImpWhile SpecImpProgram]
                      -> [SpecImpProgram]
                      -> [SpecImpProgram]
                      -> Assertion
                      -> Ceili Assertion
useAnnotatedInvariant invariant stepStrategy env aloops eloops aprogs' eprogs' post = do
  wpInvar <- relBackwardPT stepStrategy env (map body aloops) (map body eloops) invariant
  let conds = map condA (aloops ++ eloops)
  isSufficient <- checkValidB $ Imp (And $ invariant:(map Not conds)) post
  isInvariant  <- checkValidB $ Imp (And $ invariant:conds) wpInvar
  -- TODO: Lockstep
  -- TODO: Variant
  case (isSufficient, isInvariant) of
    (True, True) -> do
      log_d "[RelationalPTS] Annotated loop invariant is sufficient and invariant"
      relBackwardPT stepStrategy env aprogs' eprogs' invariant
    (False, _)   -> do
      log_e "[RelationalPTS] Annotated loop invariant insufficient to establish post"
      return AFalse
    (_, False)   -> do
      log_e "[RelationalPTS] Annotated loop invariant is not invariant on loop body"
      return AFalse

inferInvariant :: BackwardStepStrategy
               -> SpecImpEnv SpecImpProgram
               -> [ImpWhile SpecImpProgram]
               -> [ImpWhile SpecImpProgram]
               -> [SpecImpProgram]
               -> [SpecImpProgram]
               -> Assertion
               -> Ceili Assertion
inferInvariant stepStrategy env aloops eloops aprogs' eprogs' post =
  let
    bodies = ProgramRelation (map body aloops) (map body eloops)
    conds = And $ map condA (aloops ++ eloops)
    -- TODO: Lockstep
    -- TODO: Variant
    extractTests = Set.unions . catMaybes . map tests
    atests = extractTests aloops
    etests = extractTests eloops
    headStates = case (Set.null atests, Set.null etests) of
      (True,  True)  -> []
      (False, True)  -> Set.toList atests
      (True,  False) -> Set.toList etests
      (False, False) -> map (\(x, y) -> And [x, y])
                        $ Set.toList $ Set.cartesianProduct atests etests
  in case headStates of
    [] -> throwError "Insufficient test head states for while loop, did you run populateTestStates?"
    _  -> do
      result <- Pie.loopInvGen (relBackwardPT' stepStrategy) env conds bodies post headStates
      case result of
        Just inv -> relBackwardPT stepStrategy env aprogs' eprogs' inv
        Nothing -> do
          log_e "Unable to infer loop invariant, proceeding with False"
          return AFalse -- TODO: Fall back to single stepping over loops.

body :: ImpWhile e -> e
body (ImpWhile _ b _) = b

condA :: ImpWhile e -> Assertion
condA (ImpWhile c _ _) = bexpToAssertion c

tests :: ImpWhile e -> Maybe (Set Assertion)
tests (ImpWhile _ _ meta) = iwm_testStates meta

invar :: ImpWhile e -> Maybe Assertion
invar (ImpWhile _ _ meta) = iwm_invariant meta


---------------------------
-- Relational "Programs" --
---------------------------

data ProgramRelation = ProgramRelation { rp_aprogs :: [SpecImpProgram]
                                       , rp_eprogs :: [SpecImpProgram]
                                       } deriving Show

instance CollectableNames ProgramRelation where
  namesIn (ProgramRelation aprogs eprogs) = Set.union (namesIn aprogs) (namesIn eprogs)
