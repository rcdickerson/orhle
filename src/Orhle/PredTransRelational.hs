module Orhle.PredTransRelational
  ( wpLoopFusion
  , spLoopFusion
  ) where

import           Ceili.Assertion ( Assertion(..) )
import qualified Ceili.Assertion as A
import qualified Ceili.InvariantInference.Pie as Pie
import qualified Ceili.Name as Name
import qualified Data.Set as Set
import           Orhle.PredTransTypes
import           Orhle.Triple
import           Orhle.VerifierEnv


wpLoopFusion :: LoopFusion -> Assertion -> Verification Assertion
wpLoopFusion fusion post = do
  let abodies   = map rl_body $ rlf_aloops fusion
      ebodies   = map rl_body $ rlf_eloops fusion
      aconds    = map rl_condAssertion $ rlf_aloops fusion
      econds    = map rl_condAssertion $ rlf_eloops fusion
      anconds   = map A.Not aconds
      enconds   = map A.Not econds
      allBodies = abodies ++ ebodies
      allConds  = aconds ++ econds
      allNConds = anconds ++ enconds
      varSet    = Set.unions $ map Name.namesIn allConds ++ map Name.namesIn allBodies
      vars      = Set.toList varSet
  invar <- case rlf_invar fusion of
             A.Hole _ -> do
               dif <- envGetDefaultInvarFilter
               Inf.inferRevFusionInvariant (Inf.BackwardHoudini dif post) fusion
             _        -> return $ rlf_invar fusion
  freshVars     <- envFreshenAll vars
  let freshen    = Name.substituteAll vars freshVars
  let qNames     = map (\n -> TypedName n Int) freshVars
  let impPost    = freshen $ A.Imp (A.And $ invar:allNConds) post
  let decMeasure = case abodies of
                     [] -> let
                       measures = map rl_measure $ rlf_eloops fusion
                       nextMeasures = map (Name.substituteAll vars freshVars) measures
                       decConds = map (uncurry A.Lt) $ zip measures nextMeasures
                       in A.And decConds
                     _  -> ATrue
  let bodyTrip   = RevRhleTriple (A.And $ invar:allConds) abodies ebodies (A.And [invar, decMeasure])
  stepStrat     <- envBackwardStepStrat
  inductive     <- (stepStrat bodyTrip) >>= (return . freshen . uncurry A.Imp)
  let sameIters = freshen $ A.Imp (A.And [invar, (A.Not $ A.And allConds)]) (A.And allNConds)
  return $ A.And [ invar, A.Forall qNames impPost, A.Forall qNames inductive, A.Forall qNames sameIters]
