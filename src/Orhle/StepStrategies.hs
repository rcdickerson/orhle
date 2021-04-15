module Orhle.StepStrategies
  ( backwardDisallowed
  , backwardWithFusion
  , forwardDisallowed
  , forwardWithFusion
  ) where

import           Data.List ( partition )
import           Data.Map  ( Map )
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe )
import           Orhle.Assertion ( Assertion )
import qualified Orhle.Assertion as A
import           Orhle.Imp.ImpLanguage ( Program(..) )
import qualified Orhle.Imp as Imp
import qualified Orhle.PredTransSingle as PTS
import qualified Orhle.PredTransRelational as PTR
import           Orhle.PredTransTypes
import           Orhle.SMTString ( showSMT )
import           Orhle.Triple
import           Orhle.VerifierEnv

backwardDisallowed :: BackwardStepStrategy
backwardDisallowed _ = throwError "Backward stepping not allowed."

forwardDisallowed :: ForwardStepStrategy
forwardDisallowed _ = throwError "Forward stepping not allowed."


--------------------------
-- Backward with Fusion --
--------------------------

backwardWithFusion :: BackwardStepStrategy
backwardWithFusion rawTriple =
  let triple = filterEmptyRev rawTriple
  in case triple of
    RevRhleTriple pre [] [] post -> return $ (pre, post)
    _                            -> backstepWithFusion triple >>= backwardWithFusion

backstepWithFusion :: RevRhleTriple -> Verification RevRhleTriple
backstepWithFusion triple = do
  result <- trySequence triple [ lookForBNonLoop
                               , lookForBLoopFusion
                               , lookForBStepAny
                               ]
  case result of
    Just triple' -> return triple'
    Nothing      -> throwError "Could not find a step to take."

lookForBNonLoop :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
lookForBNonLoop (RevRhleTriple pre aprogs eprogs post) = let
  (aloops, as) = partition Imp.headIsLoop aprogs
  (eloops, es) = partition Imp.headIsLoop eprogs
  in case (as, es) of
    ([], []) -> return Nothing
    (_, eprog:rest) -> do
      let (hd, eprog') = Imp.headProg eprog
      post' <- PTS.weakestPreQ VExistential hd post
      return $ Just $ RevRhleTriple pre aprogs (eprog':(rest ++ eloops)) post'
    (aprog:rest, _) -> do
      let (hd, aprog') = Imp.headProg aprog
      post' <- PTS.weakestPreQ VUniversal hd post
      return $ Just $ RevRhleTriple pre (aprog':(rest ++ aloops)) eprogs post'

lookForBLoopFusion :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
lookForBLoopFusion triple@(RevRhleTriple pre aprogs eprogs post) = let
  (aLoops, aNonLoops) = partition Imp.headIsLoop aprogs
  (eLoops, eNonLoops) = partition Imp.headIsLoop eprogs
  in if (not $ null $ aNonLoops ++ eNonLoops)
    then return Nothing
    else do
      let aheads       = map Imp.headProg aprogs
          eheads       = map Imp.headProg eprogs
          aloopMap     = categorizeByInvar $ map fst aheads
          eloopMap     = categorizeByInvar $ map fst eheads
          (tag, loops) = head $ Map.toAscList aloopMap ++ Map.toAscList eloopMap
          invar        = rl_invar . head $ loops
          aloops       = fromMaybe [] $ Map.lookup tag aloopMap
          eloops       = fromMaybe [] $ Map.lookup tag eloopMap
          fusion       = RevLoopFusion aloops eloops (map snd aheads) (map snd eheads) pre post triple invar
      post' <- PTR.wpLoopFusion fusion post
      return $ Just $ RevRhleTriple pre (rlf_arest fusion) (rlf_erest fusion) post'

lookForBStepAny :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
lookForBStepAny (RevRhleTriple pre aprogs eprogs post) =
  case (aprogs, eprogs) of
    ([], []) -> return Nothing
    (_, eprog:rest) -> do
      let (hd, eprog') = Imp.headProg eprog
      post' <- PTS.weakestPreQ VExistential hd post
      return $ Just $ RevRhleTriple pre aprogs (eprog':rest) post'
    (aprog:rest, _) -> do
      let (hd, aprog') = Imp.headProg aprog
      post' <- PTS.weakestPreQ VUniversal hd post
      return $ Just $ RevRhleTriple pre (aprog':rest) eprogs post'

categorizeByInvar :: [RevProgram] -> Map String [RevLoop]
categorizeByInvar programs = let
  taggedLoop prog = case prog of
    SWhile condB body (invar@(A.Hole (A.HoleId hid _)), _) -> ("hole", RevLoop body (Imp.bexpToAssertion condB) condB (Just hid) invar)
    SWhile condB body (invar, _) -> (showSMT invar, RevLoop body (Imp.bexpToAssertion condB) condB Nothing invar)
    _ -> error $ "Program is not a loop: " ++ show prog
  addLoop loop maybeList = case maybeList of
    Nothing -> Just [loop]
    Just ls -> Just (loop:ls)
  updateMap prog m =
    let (tag, loop) = taggedLoop prog
    in Map.alter (addLoop loop) tag m
  in foldr updateMap Map.empty programs


-------------------------
-- Forward with Fusion --
-------------------------

-- TODO: DRY this up

forwardWithFusion :: ForwardStepStrategy
forwardWithFusion rawTriple =
  let triple = filterEmptyTrip rawTriple
  in case triple of
    RhleTriple pre [] [] post -> return $ (pre, post)
    _                         -> stepWithFusion triple >>= forwardWithFusion

stepWithFusion :: RhleTriple -> Verification RhleTriple
stepWithFusion triple = do
  result <- trySequence triple [ lookForFLoopFusion
                               , lookForFStepNonLoop
                               , lookForFStepAny
                               ]
  case result of
    Just triple' -> return triple'
    Nothing      -> throwError "Could not find a step to take."

lookForFLoopFusion :: RhleTriple -> Verification (Maybe RhleTriple)
lookForFLoopFusion triple@(RhleTriple pre aprogs eprogs post) = let
  (aLoops, aNonLoops) = partition Imp.headIsLoop aprogs
  (eLoops, eNonLoops) = partition Imp.headIsLoop eprogs
  in if (not $ null $ aNonLoops ++ eNonLoops)
    then return Nothing
    else do
      let aheads = map Imp.headProg aprogs
          eheads = map Imp.headProg eprogs
          aloops = map (progToLoop . fst) aheads
          eloops = map (progToLoop . fst) eheads
          -- TODO: verify synchronous stepping
          ((SWhile _ _ (inv, _)), _)  -- TODO: only fuse on identical invariants
            = Imp.headProg $ head $ (aLoops ++ eLoops)
          fusion = LoopFusion aloops eloops (map snd aheads) (map snd eheads) pre post triple inv
      post' <- PTR.spLoopFusion fusion post
      return $ Just $ RhleTriple pre (lf_arest fusion) (lf_erest fusion) post'

lookForFStepNonLoop :: RhleTriple -> Verification (Maybe RhleTriple)
lookForFStepNonLoop (RhleTriple pre aprogs eprogs post) = let
  (aloops, as) = partition Imp.headIsLoop aprogs
  (eloops, es) = partition Imp.headIsLoop eprogs
  in case (as, es) of
    ([], []) -> return Nothing
    (_, eprog:rest) -> do
      let (hd, eprog') = Imp.headProg eprog
      post' <- PTS.weakestPreQ VExistential hd post
      return $ Just $ RhleTriple pre aprogs (eprog':(rest ++ eloops)) post'
    (aprog:rest, _) -> do
      let (hd, aprog') = Imp.headProg aprog
      post' <- PTS.weakestPreQ VUniversal hd post
      return $ Just $ RhleTriple pre (aprog':(rest ++ aloops)) eprogs post'

lookForFStepAny :: RhleTriple -> Verification (Maybe RhleTriple)
lookForFStepAny (RhleTriple pre aprogs eprogs post) =
  case (aprogs, eprogs) of
    ([], []) -> return Nothing
    (_, eprog:rest) -> do
      let (hd, eprog') = Imp.headProg eprog
      post' <- PTS.weakestPreQ VExistential hd post
      return $ Just $ RhleTriple pre aprogs (eprog':rest) post'
    (aprog:rest, _) -> do
      let (hd, aprog') = Imp.headProg aprog
      post' <- PTS.weakestPreQ VUniversal hd post
      return $ Just $ RhleTriple pre (aprog':rest) eprogs post'

progToLoop :: Program -> Loop
progToLoop program = case program of
  SWhile condB body (invar@(A.Hole (A.HoleId hid _)), _) ->
    Loop body (Imp.bexpToAssertion condB) condB (Just hid) invar
  _ -> error $ "Program is not a loop with missing invariant: " ++ show program


---------------
-- Utilities --
---------------

trySequence :: a -> [a -> Verification (Maybe a)] -> Verification (Maybe a)
trySequence _ [] = return Nothing
trySequence x (v:vs) = do
  result <- v x
  case result of
    Just _  -> return result
    Nothing -> trySequence x vs
