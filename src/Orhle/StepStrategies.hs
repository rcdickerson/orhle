{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}

module Orhle.StepStrategies
  ( BackwardStepStrategy
  , Selection(..)
  , Step(..)
  , backwardDisallowed
  , backwardWithFusion
  ) where

import Ceili.CeiliEnv
import Ceili.Language.Compose
import Data.Maybe ( catMaybes )
import Orhle.SpecImp

data Selection = UniversalStatement SpecImpProgram
               | ExistentialStatement SpecImpProgram
               | LoopFusion [SpecImpProgram] [SpecImpProgram]
               | NoSelectionFound

data Step = Step { step_selection :: Selection
                 , step_aprogs    :: [SpecImpProgram]
                 , step_eprogs    :: [SpecImpProgram]
                 }

type BackwardStepStrategy = [SpecImpProgram] -> [SpecImpProgram] -> Ceili Step

backwardDisallowed :: BackwardStepStrategy
backwardDisallowed _ _ = throwError "Backward stepping not allowed."

--------------------------
-- Backward with Fusion --
--------------------------

backwardWithFusion :: BackwardStepStrategy
backwardWithFusion aprogs eprogs = return $
  scanPossibleSteps aprogs eprogs [ loopFusion
                                  , stepExistential
                                  , stepUniversal
                                  ]


type PossibleStep = [LastStatement] -> [LastStatement] -> Maybe Step

scanPossibleSteps :: [SpecImpProgram] -> [SpecImpProgram] -> [PossibleStep] -> Step
scanPossibleSteps aprogs eprogs options =
  let
    lastAs = map lastStatement aprogs
    lastEs = map lastStatement eprogs
    steps  = catMaybes $ map (\try -> try lastAs lastEs) options
  in case steps of
       []     -> Step NoSelectionFound aprogs eprogs
       step:_ -> step

loopFusion :: PossibleStep
loopFusion = error "unimplemented"

stepExistential :: PossibleStep
stepExistential = error "unimplemented"

stepUniversal :: PossibleStep
stepUniversal = error "unimplemented"

data LastStatement = LastStatement { ls_last :: SpecImpProgram
                                   , ls_rest :: Maybe SpecImpProgram
                                   }

class FindLastStatement e where
  lastStatement :: e -> LastStatement
instance (FindLastStatement (f e), FindLastStatement (g e)) => FindLastStatement ((f :+: g) e) where
  lastStatement (Inl f) = lastStatement f
  lastStatement (Inr g) = lastStatement g
instance FindLastStatement SpecImpProgram where
  lastStatement (In p) = lastStatement p
instance FindLastStatement (ImpSkip e) where
  lastStatement ImpSkip = LastStatement impSkip Nothing
instance FindLastStatement (ImpAsgn e) where
  lastStatement (ImpAsgn lhs rhs) = LastStatement (impAsgn lhs rhs) Nothing
instance FindLastStatement (ImpSeq SpecImpProgram) where
  lastStatement (ImpSeq stmts) = case stmts of
    []     -> LastStatement impSkip Nothing
    (s:[]) -> LastStatement s Nothing
    _      -> let (ss, t) = splitTail stmts
                  LastStatement lastT mRest = lastStatement t
              in case mRest of
                   Nothing   -> LastStatement lastT (Just $ impSeq ss)
                   Just rest -> LastStatement lastT (Just $ impSeq $ ss ++ [rest])
instance FindLastStatement (ImpIf SpecImpProgram) where
  lastStatement (ImpIf c t e) = LastStatement (impIf c t e) Nothing
instance FindLastStatement (ImpWhile SpecImpProgram) where
  lastStatement (ImpWhile c body meta) = LastStatement (impWhileWithMeta c body meta) Nothing
instance FindLastStatement (ImpCall SpecImpProgram) where
  lastStatement (ImpCall cid params assignees) = LastStatement (impCall cid params assignees) Nothing
instance FindLastStatement (ImpSpecCall SpecImpProgram) where
  lastStatement (ImpSpecCall cid params assignees) = LastStatement (impSpecCall cid params assignees) Nothing

splitTail :: [a] -> ([a], a)
splitTail list = case list of
  []     -> error "Empty list"
  (x:[]) -> ([], x)
  (x:xs) -> let (rest, t) = splitTail xs
            in (x:rest, t)

--   let triple = filterEmptyRev rawTriple
--   in case triple of
--     RevRhleTriple pre [] [] post -> return $ (pre, post)
--     _                            -> backstepWithFusion triple >>= backwardWithFusion

-- backstepWithFusion :: RevRhleTriple -> Verification RevRhleTriple
-- backstepWithFusion triple = do
--   result <- trySequence triple [ lookForBNonLoop
--                                , lookForBLoopFusion
--                                , lookForBStepAny
--                                ]
--   case result of
--     Just triple' -> return triple'
--     Nothing      -> throwError "Could not find a step to take."

-- lookForBNonLoop :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
-- lookForBNonLoop (RevRhleTriple pre aprogs eprogs post) = let
--   (aloops, as) = partition Imp.headIsLoop aprogs
--   (eloops, es) = partition Imp.headIsLoop eprogs
--   in case (as, es) of
--     ([], []) -> return Nothing
--     (aprog:rest, _) -> do
--       let (hd, aprog') = Imp.headProg aprog
--       post' <- PTS.weakestPreQ VUniversal hd post
--       return $ Just $ RevRhleTriple pre (aprog':(rest ++ aloops)) eprogs post'
--     (_, eprog:rest) -> do
--       let (hd, eprog') = Imp.headProg eprog
--       post' <- PTS.weakestPreQ VExistential hd post
--       return $ Just $ RevRhleTriple pre aprogs (eprog':(rest ++ eloops)) post'

-- lookForBLoopFusion :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
-- lookForBLoopFusion triple@(RevRhleTriple pre aprogs eprogs post) = let
--   (aLoops, aNonLoops) = partition Imp.headIsLoop aprogs
--   (eLoops, eNonLoops) = partition Imp.headIsLoop eprogs
--   in if (not $ null $ aNonLoops ++ eNonLoops)
--     then return Nothing
--     else do
--       let aheads       = map Imp.headProg aprogs
--           eheads       = map Imp.headProg eprogs
--           aloopMap     = categorizeByInvar $ map fst aheads
--           eloopMap     = categorizeByInvar $ map fst eheads
--           (tag, loops) = head $ Map.toAscList aloopMap ++ Map.toAscList eloopMap
--           invar        = rl_invar . head $ loops
--           aloops       = fromMaybe [] $ Map.lookup tag aloopMap
--           eloops       = fromMaybe [] $ Map.lookup tag eloopMap
--           fusion       = RevLoopFusion aloops eloops (map snd aheads) (map snd eheads) pre post triple invar
--       post' <- PTR.wpLoopFusion fusion post
--       return $ Just $ RevRhleTriple pre (rlf_arest fusion) (rlf_erest fusion) post'

-- lookForBStepAny :: RevRhleTriple -> Verification (Maybe RevRhleTriple)
-- lookForBStepAny (RevRhleTriple pre aprogs eprogs post) =
--   case (aprogs, eprogs) of
--     ([], []) -> return Nothing
--     (aprog:rest, _) -> do
--       let (hd, aprog') = Imp.headProg aprog
--       post' <- PTS.weakestPreQ VUniversal hd post
--       return $ Just $ RevRhleTriple pre (aprog':rest) eprogs post'
--     (_, eprog:rest) -> do
--       let (hd, eprog') = Imp.headProg eprog
--       post' <- PTS.weakestPreQ VExistential hd post
--       return $ Just $ RevRhleTriple pre aprogs (eprog':rest) post'

-- categorizeByInvar :: [RevProgram] -> Map String [RevLoop]
-- categorizeByInvar programs = let
--   taggedLoop prog = case prog of
--     SWhile condB body (invar@(A.Hole (A.HoleId hid _)), meas) -> ("hole", RevLoop body (Imp.bexpToAssertion condB) condB (Just hid) invar meas)
--     SWhile condB body (invar, meas) -> (showSMT invar, RevLoop body (Imp.bexpToAssertion condB) condB Nothing invar meas)
--     _ -> error $ "Program is not a loop: " ++ show prog
--   addLoop loop maybeList = case maybeList of
--     Nothing -> Just [loop]
--     Just ls -> Just (loop:ls)
--   updateMap prog m =
--     let (tag, loop) = taggedLoop prog
--     in Map.alter (addLoop loop) tag m
--   in foldr updateMap Map.empty programs


-------------------------
-- Forward with Fusion --
-------------------------

-- TODO: DRY this up

-- forwardWithFusion :: ForwardStepStrategy
-- forwardWithFusion rawTriple =
--   let triple = filterEmptyTrip rawTriple
--   in case triple of
--     RhleTriple pre [] [] post -> return $ (pre, post)
--     _                         -> stepWithFusion triple >>= forwardWithFusion

-- stepWithFusion :: RhleTriple -> Verification RhleTriple
-- stepWithFusion triple = do
--   result <- trySequence triple [ lookForFLoopFusion
--                                , lookForFStepNonLoop
--                                , lookForFStepAny
--                                ]
--   case result of
--     Just triple' -> return triple'
--     Nothing      -> throwError "Could not find a step to take."

-- lookForFLoopFusion :: RhleTriple -> Verification (Maybe RhleTriple)
-- lookForFLoopFusion triple@(RhleTriple pre aprogs eprogs post) = let
--   (aLoops, aNonLoops) = partition Imp.headIsLoop aprogs
--   (eLoops, eNonLoops) = partition Imp.headIsLoop eprogs
--   in if (not $ null $ aNonLoops ++ eNonLoops)
--     then return Nothing
--     else do
--       let aheads = map Imp.headProg aprogs
--           eheads = map Imp.headProg eprogs
--           aloops = map (progToLoop . fst) aheads
--           eloops = map (progToLoop . fst) eheads
--           -- TODO: verify synchronous stepping
--           ((SWhile _ _ (inv, _)), _)  -- TODO: only fuse on identical invariants
--             = Imp.headProg $ head $ (aLoops ++ eLoops)
--           fusion = LoopFusion aloops eloops (map snd aheads) (map snd eheads) pre post triple inv
--       post' <- PTR.spLoopFusion fusion post
--       return $ Just $ RhleTriple pre (lf_arest fusion) (lf_erest fusion) post'

-- lookForFStepNonLoop :: RhleTriple -> Verification (Maybe RhleTriple)
-- lookForFStepNonLoop (RhleTriple pre aprogs eprogs post) = let
--   (aloops, as) = partition Imp.headIsLoop aprogs
--   (eloops, es) = partition Imp.headIsLoop eprogs
--   in case (as, es) of
--     ([], []) -> return Nothing
--     (_, eprog:rest) -> do
--       let (hd, eprog') = Imp.headProg eprog
--       post' <- PTS.weakestPreQ VExistential hd post
--       return $ Just $ RhleTriple pre aprogs (eprog':(rest ++ eloops)) post'
--     (aprog:rest, _) -> do
--       let (hd, aprog') = Imp.headProg aprog
--       post' <- PTS.weakestPreQ VUniversal hd post
--       return $ Just $ RhleTriple pre (aprog':(rest ++ aloops)) eprogs post'

-- lookForFStepAny :: RhleTriple -> Verification (Maybe RhleTriple)
-- lookForFStepAny (RhleTriple pre aprogs eprogs post) =
--   case (aprogs, eprogs) of
--     ([], []) -> return Nothing
--     (_, eprog:rest) -> do
--       let (hd, eprog') = Imp.headProg eprog
--       post' <- PTS.weakestPreQ VExistential hd post
--       return $ Just $ RhleTriple pre aprogs (eprog':rest) post'
--     (aprog:rest, _) -> do
--       let (hd, aprog') = Imp.headProg aprog
--       post' <- PTS.weakestPreQ VUniversal hd post
--       return $ Just $ RhleTriple pre (aprog':rest) eprogs post'

-- progToLoop :: Program -> Loop
-- progToLoop program = case program of
--   SWhile condB body (invar@(A.Hole (A.HoleId hid _)), _) ->
--     Loop body (Imp.bexpToAssertion condB) condB (Just hid) invar
--   _ -> error $ "Program is not a loop with missing invariant: " ++ show program


---------------
-- Utilities --
---------------

-- trySequence :: a -> [a -> Verification (Maybe a)] -> Verification (Maybe a)
-- trySequence _ [] = return Nothing
-- trySequence x (v:vs) = do
--   result <- v x
--   case result of
--     Just _  -> return result
--     Nothing -> trySequence x vs
