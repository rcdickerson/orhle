module Orhle.RelationalPTS
  ( relBackwardPTS
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import qualified Ceili.InvariantInference.Pie as Pie
import Orhle.SpecImp
import Orhle.StepStrategy


relBackwardPTS :: BackwardStepStrategy
               -> SpecImpEnv
               -> [SpecImpProgram]
               -> [SpecImpProgram]
               -> Assertion
               -> Ceili Assertion
relBackwardPTS stepStrategy specs aprogs eprogs post = do
  error "unimplemented"

-- wpLoopFusion :: LoopFusion -> Assertion -> Verification Assertion
-- wpLoopFusion fusion post = do
--   let abodies   = map rl_body $ rlf_aloops fusion
--       ebodies   = map rl_body $ rlf_eloops fusion
--       aconds    = map rl_condAssertion $ rlf_aloops fusion
--       econds    = map rl_condAssertion $ rlf_eloops fusion
--       anconds   = map A.Not aconds
--       enconds   = map A.Not econds
--       allBodies = abodies ++ ebodies
--       allConds  = aconds ++ econds
--       allNConds = anconds ++ enconds
--       varSet    = Set.unions $ map Name.namesIn allConds ++ map Name.namesIn allBodies
--       vars      = Set.toList varSet
--   invar <- case rlf_invar fusion of
--              A.Hole _ -> do
--                dif <- envGetDefaultInvarFilter
--                Inf.inferRevFusionInvariant (Inf.BackwardHoudini dif post) fusion
--              _        -> return $ rlf_invar fusion
--   freshVars     <- envFreshenAll vars
--   let freshen    = Name.substituteAll vars freshVars
--   let qNames     = map (\n -> TypedName n Int) freshVars
--   let impPost    = freshen $ A.Imp (A.And $ invar:allNConds) post
--   let decMeasure = case abodies of
--                      [] -> let
--                        measures = map rl_measure $ rlf_eloops fusion
--                        nextMeasures = map (Name.substituteAll vars freshVars) measures
--                        decConds = map (uncurry A.Lt) $ zip measures nextMeasures
--                        in A.And decConds
--                      _  -> ATrue
--   let bodyTrip   = RevRhleTriple (A.And $ invar:allConds) abodies ebodies (A.And [invar, decMeasure])
--   stepStrat     <- envBackwardStepStrat
--   inductive     <- (stepStrat bodyTrip) >>= (return . freshen . uncurry A.Imp)
--   let sameIters = freshen $ A.Imp (A.And [invar, (A.Not $ A.And allConds)]) (A.And allNConds)
--   return $ A.And [ invar, A.Forall qNames impPost, A.Forall qNames inductive, A.Forall qNames sameIters]
