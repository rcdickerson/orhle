module Orhle.PredTransRelational
  ( wpLoopFusion
  , spLoopFusion
  ) where

import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion(..) )
import qualified Orhle.Assertion as A
import qualified Orhle.InvariantInference as Inf
import qualified Orhle.Name as Name
import           Orhle.PredTransTypes
import           Orhle.Triple
import           Orhle.VerifierEnv

wpLoopFusion :: RevLoopFusion -> Assertion -> Verification Assertion
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
  let qNames     = Name.toIntNames freshVars
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

spLoopFusion :: LoopFusion -> Assertion -> Verification Assertion
spLoopFusion fusion pre = do
  let abodies   = map l_body $ lf_aloops fusion
      ebodies   = map l_body $ lf_eloops fusion
      aconds    = map l_condAssertion $ lf_aloops fusion
      econds    = map l_condAssertion $ lf_eloops fusion
      anconds   = map A.Not aconds
      enconds   = map A.Not econds
      allBodies = abodies ++ ebodies
      allConds  = aconds ++ econds
      allNConds = anconds ++ enconds
      varSet    = Set.unions $ map Name.namesIn allConds ++ map Name.namesIn allBodies
      vars      = Set.toList varSet
  invar <- case lf_invar fusion of
--             A.Hole _ -> do
--               firstPre <- envGetLoopSP
--               Inf.inferInvariants (BackwardHoudini _) (RhleTriple _)
--               let afilter assertion = checkValid False $ A.Imp firstPre assertion
--               invar <- findInvarWithFilter afilter allConds abodies ebodies post
--               case invar of
--                 Nothing     -> throwError "Unable to synthesize loop invariant"
--                 Just result -> return result
             _  -> return $ lf_invar fusion
  freshVars    <- envFreshenAll vars
  let freshen   = Name.substituteAll vars freshVars
  let qNames    = Name.toIntNames freshVars
  let followsFromPre = freshen $ A.Imp pre invar
  let bodyTrip  = RhleTriple (A.And $ invar:allConds) abodies ebodies invar
  stepStrat    <- envForwardStepStrat
  inductive    <- (stepStrat bodyTrip) >>= (return . freshen . uncurry A.Imp)
  let sameIters = freshen $ A.Imp (A.And [invar, (A.Not $ A.And allConds)]) (A.And allNConds)
  -- VCs: [A.Forall qNames inductive, A.Forall qNames sameIters A.Forall qNames impPost]
  return $ A.And (invar:allNConds)
