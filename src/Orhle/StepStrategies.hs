module Orhle.StepStrategies
  ( backwardDisallowed
  , backwardWithFusion
  , forwardDisallowed
  , forwardWithFusion
  ) where

import           Data.List ( partition )
import qualified Orhle.Assertion as A
import           Orhle.Imp.ImpLanguage ( Program(..) )
import qualified Orhle.Imp as Imp
import qualified Orhle.PredTransSingle as PTS
import qualified Orhle.PredTransRelational as PTR
import           Orhle.PredTransTypes
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
  result <- trySequence triple [ lookForBLoopFusion
                               , lookForBStepNonLoop
                               , lookForBStepAny
                               ]
  case result of
    Just triple' -> return triple'
    Nothing      -> throwError "Could not find a step to take."

lookForBLoopFusion :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
lookForBLoopFusion triple@(RevRhleTriple pre aprogs eprogs post) = let
  (aLoops, aNonLoops) = partition Imp.headIsLoop aprogs
  (eLoops, eNonLoops) = partition Imp.headIsLoop eprogs
  in if (not $ null $ aNonLoops ++ eNonLoops)
    then return Nothing
    else do
      let aheads = map Imp.headProg aprogs
          eheads = map Imp.headProg eprogs
          aloops = map (progToRevLoop . fst) aheads
          eloops = map (progToRevLoop . fst) eheads
          -- TODO: verify synchronous stepping
          ((SWhile _ _ (inv, _)), _)  -- TODO: only fuse on identical invariants
            = Imp.headProg $ head $ (aLoops ++ eLoops)
          fusion = RevLoopFusion aloops eloops (map snd aheads) (map snd eheads) pre post triple inv
      post' <- PTR.wpLoopFusion fusion post
      return $ Just $ RevRhleTriple pre (rlf_arest fusion) (rlf_erest fusion) post'

lookForBStepNonLoop :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
lookForBStepNonLoop (RevRhleTriple pre aprogs eprogs post) = let
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

progToRevLoop :: RevProgram -> RevLoop
progToRevLoop program = case program of
  SWhile condB body (A.Hole (A.HoleId hid _), _) ->
    RevLoop body (Imp.bexpToAssertion condB) condB hid
  _ -> error $ "Program is not a loop with missing invariant: " ++ show program


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
  SWhile condB body (A.Hole (A.HoleId hid _), _) ->
    Loop body (Imp.bexpToAssertion condB) condB hid
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
