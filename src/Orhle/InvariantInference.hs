module Orhle.InvariantInference
  ( InferenceStrategy(..)
  , inferRevFusionInvariant
  ) where

import           Control.Concurrent.Timeout
import           Control.Monad ( filterM )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Map  ( Map )
import qualified Data.Map as Map
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion(..) )
import qualified Orhle.Assertion as A
import           Orhle.Imp ( Program(..) )
import qualified Orhle.Imp as Imp
import           Orhle.LinearInequalities ( linearInequalities )
import           Orhle.Name  ( Name(..), TypedName(..), namesIn )
import qualified Orhle.Name as Name
import           Orhle.PredTransTypes
import qualified Orhle.SMT as SMT
import           Orhle.SMTString ( showSMT )
import           Orhle.Triple ( RhleTriple(..), RevRhleTriple(..) )
import           Orhle.VerifierEnv

data InferenceStrategy = DisallowHoles
                       | BackwardHoudini { candidateFilter :: Assertion
                                         , wp_post         :: Assertion }

inferRevFusionInvariant :: InferenceStrategy -> RevLoopFusion -> Verification Assertion
inferRevFusionInvariant strategy fusion = case strategy of
  DisallowHoles                -> throwError "Encountered missing invariant annotation."
  BackwardHoudini cfilter post -> performRevFusionHoudini fusion cfilter post

---------------------
-- BackwardHoudini --
---------------------

performRevFusionHoudini :: RevLoopFusion -> Assertion -> Assertion -> Verification Assertion
performRevFusionHoudini fusion cfilter post = do
  envLog $ "Inferring invariant via backward houdini..."
  candidates <- findCandidates (rlf_origTrip fusion) cfilter
  findRevFusionInvar candidates fusion post

findCandidates :: RevRhleTriple -> Assertion -> Verification (Set Assertion)
findCandidates (RevRhleTriple pre aprogs eprogs post) cfilter = do
  let progs = aprogs ++ eprogs
  let lits  = Set.unions $ (map Imp.plits progs)
  envLog $ "  Number of lits: " ++ (show $ Set.size lits)
  let varNames = Set.unions $ (namesIn pre):(namesIn post):(map namesIn progs)
  let vars     = Set.map (\n -> TypedName n Name.Int) varNames
  envLog $ "  Number of vars: " ++ (show $ Set.size vars)
  let candidates = linearInequalities 2 lits vars
  envLog $ "  Candidates size: " ++ (show $ Set.size candidates)
  envLog $ "  Filtering on: " ++ (showSMT $ cfilter)
  let afilter assertion = checkValid False $ A.Imp cfilter assertion
  filtered <- filterM afilter $ Set.toList candidates
  envLog $ "  Filtered size: " ++ (show $ length filtered)
  --envLog "  Filtered clauses:" >> mapM_ envLog (map showSMT filtered)
  return $ Set.fromList filtered

findRevFusionInvar :: Set Assertion -> RevLoopFusion -> Assertion -> Verification Assertion
findRevFusionInvar candidates fusion loopPost = do
  let nconds = A.And $
        map A.Not $
        map rl_condAssertion $ (rlf_aloops fusion) ++ (rlf_eloops fusion)
  let aBodies = map rl_body $ rlf_aloops fusion
  let eBodies = map rl_body $ rlf_eloops fusion
  let computeWP a = do
        bstep <- envBackwardStepStrat
        (_, wp) <- bstep $ RevRhleTriple A.ATrue (freezeNames aBodies) (freezeNames eBodies) a
        return wp
  inductive <- houdini (freezeNames $ Set.toList candidates) (freezeNames $ A.Imp nconds loopPost) computeWP
  envLog $ "  Inductive size: " ++ (show $ length inductive)
  envLog "  Inductive clauses:" >> mapM_ envLog (map showSMT inductive)
  case length inductive of
    0 -> do envLog "Unable to infer loop invariant, using True." >> return A.ATrue
    _ -> return $ thawNames $ A.And inductive

houdini :: [Assertion]
        -> Assertion
        -> (Assertion -> Verification Assertion)
        -> Verification [Assertion]
houdini candidates loopNConds computeWP = do
    envLog $ "Starting houdini pass with " ++ (show $ length candidates) ++ " candidate clauses."
    invariant' <- computeWP $ A.And $ candidates
    let invariant = zeroNames invariant'
    envLog $ "  Proposed Invariant: " ++ (showSMT invariant)
    let isInductive a = checkValid False $ A.Imp invariant a
    inductive <- filterM isInductive candidates
    if (length inductive == length candidates)
      then return candidates
      else houdini inductive loopNConds computeWP

freezeNames :: Name.MappableNames a => a -> a
freezeNames = id -- Name.mapNames $ \n -> Name (show n) 0

thawNames :: Name.MappableNames a => a -> a
thawNames = id --Name.mapNames $ \(Name n _) -> Name.fromString n

zeroNames :: Name.MappableNames a => a -> a
zeroNames = id --Name.mapNames $ \(Name n _) -> Name n 0

---------------
-- Utilities --
---------------

countHoles :: Imp.Program -> Int
countHoles prog = case prog of
  SSkip       -> 0
  SAsgn _ _   -> 0
  SCall _ _ _ -> 0
  SSeq  ss    -> sum $ map countHoles ss
  SIf _ t e   -> (countHoles t) + (countHoles e)
  SWhile _ body (inv, _) ->
    case inv of
      Hole _ -> 1 + (countHoles body)
      _      -> 0 + (countHoles body)


countAllHoles :: [Imp.Program] -> Int
countAllHoles = sum . map countHoles

countAllHolesInTrip :: RhleTriple -> Int
countAllHolesInTrip (RhleTriple _ aprogs eprogs _) = countAllHoles $ aprogs ++ eprogs

fillInvHole :: Int -> Assertion -> Program -> Program
fillInvHole holeId fill prog = let
  fillRec = fillInvHole holeId fill
  in case prog of
    SSkip                    -> Imp.SSkip
    SAsgn _ _                -> prog
    SSeq ps                  -> Imp.SSeq $ map fillRec ps
    SIf c p1 p2              -> Imp.SIf c (fillRec p1) (fillRec p2)
    SCall _ _ _              -> prog
    SWhile c body (inv, var) ->
      let inv' = case inv of
            Hole (A.HoleId hid _) -> if hid == holeId then fill else inv
            _                     -> inv
      in Imp.SWhile c (fillRec body) (inv', var)

fillInvHoles :: Map Int Assertion -> [Program] -> [Program]
fillInvHoles mapping =
  let doFills assertion = foldr (uncurry fillInvHole) assertion (Map.assocs mapping)
  in map doFills

fillTripInvHoles :: Map Int Assertion -> RhleTriple -> RhleTriple
fillTripInvHoles mapping (RhleTriple pre aprogs eprogs post) =
  RhleTriple pre (fillInvHoles mapping aprogs) (fillInvHoles mapping eprogs) post

withTimeout t = liftIO $ timeout (1000000 * 2) t

checkValid :: Bool -> Assertion -> Verification Bool
checkValid envLogOutput assertion = do
  result <- withTimeout $ SMT.checkValid envLogOutput assertion
  case result of
    Nothing               -> do envLog "SMT timeout"; return False
    Just SMT.Valid        -> return True -- do envLog "SMT valid"; return True
    Just (SMT.Invalid _)  -> return False -- do envLog "SMT invalid"; return False
    Just SMT.ValidUnknown -> do envLog "SMT unknown"; return False
