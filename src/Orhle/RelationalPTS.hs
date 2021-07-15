module Orhle.RelationalPTS
  ( relBackwardPT
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Language.BExp ( bexpToAssertion )
import Ceili.Language.Imp ( ImpWhileMetadata(..) )
import Ceili.Name
import qualified Ceili.InvariantInference.Pie as Pie
import Data.Maybe ( catMaybes )
import Data.Set ( Set )
import qualified Data.Set as Set
import Orhle.SpecImp
import Orhle.StepStrategy


relBackwardPT :: BackwardStepStrategy
               -> SpecImpEnv
               -> [SpecImpProgram]
               -> [SpecImpProgram]
               -> Assertion
               -> Ceili Assertion
relBackwardPT stepStrategy env aprogs eprogs post =
  relBackwardPT' stepStrategy env (ProgramRelation aprogs eprogs) post


relBackwardPT' :: BackwardStepStrategy
               -> SpecImpEnv
               -> ProgramRelation
               -> Assertion
               -> Ceili Assertion
relBackwardPT' stepStrategy env (ProgramRelation aprogs eprogs) post = do
  Step selection aprogs' eprogs' <- stepStrategy aprogs eprogs
  case selection of
    UniversalStatement stmt -> do
      post' <- impBackwardPT (SIQ_Universal, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    ExistentialStatement stmt -> do
      post' <- impBackwardPT (SIQ_Existential, env) stmt post
      relBackwardPT stepStrategy env aprogs' eprogs' post'
    LoopFusion aloops eloops -> do
      let bodies = ProgramRelation (map body aloops) (map body eloops)
      let conds = And $ map condA (aloops ++ eloops)
      let pts = relBackwardPT' stepStrategy
      loopTests <- case catMaybes $ map tests (aloops ++ eloops) of
                     [] -> throwError "No test states for while loop, did you run populateTestStates?"
                     t  -> return $ Set.toList $ Set.unions t
      pieResult <- Pie.loopInvGen pts env conds bodies post loopTests
      case pieResult of
        Just inv -> return inv
        Nothing -> do
          log_i "Unable to infer loop invariant, proceeding with False"
          return AFalse
    NoSelectionFound -> case (aprogs', eprogs') of
                          ([], []) -> return post
                          _ -> throwError "Unable to find step"

body :: ImpWhile e -> e
body (ImpWhile _ b _) = b

condA :: ImpWhile e -> Assertion
condA (ImpWhile c _ _) = bexpToAssertion c

tests :: ImpWhile e -> Maybe (Set Assertion)
tests (ImpWhile _ _ meta) = iwm_testStates meta


---------------------------
-- Relational "Programs" --
---------------------------

data ProgramRelation = ProgramRelation { rp_aprogs :: [SpecImpProgram]
                                       , rp_eprogs :: [SpecImpProgram]
                                       }

instance CollectableNames ProgramRelation where
  namesIn (ProgramRelation aprogs eprogs) = Set.union (namesIn aprogs) (namesIn eprogs)
