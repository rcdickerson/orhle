{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Orhle.StepStrategy
  ( BackwardStepStrategy
  , Selection(..)
  , Step(..)
  , backwardDisallowed
  , backwardWithFusion
  ) where

import Ceili.CeiliEnv
import Ceili.Language.Compose
import Data.List ( partition )
import Data.Maybe ( catMaybes )
import Orhle.SpecImp
import Prettyprinter

type BackwardStepStrategy t = [SpecImpProgram t] -> [SpecImpProgram t] -> Ceili (Step t)

backwardDisallowed :: BackwardStepStrategy t
backwardDisallowed _ _ = throwError "Backward stepping not allowed."


-----------
-- Steps --
-----------

data Step t = Step { step_selection :: Selection t
                   , step_aprogs    :: [SpecImpProgram t]
                   , step_eprogs    :: [SpecImpProgram t]
                   } deriving (Show, Eq)

data Selection t = UniversalStatement (SpecImpProgram t)
                 | ExistentialStatement (SpecImpProgram t)
                 | LoopFusion [ImpWhile t (SpecImpProgram t)] [ImpWhile t (SpecImpProgram t)]
                 | NoSelectionFound
               deriving (Show, Eq)

type PossibleStep t = [SpecImpProgram t] -> [SpecImpProgram t] -> Maybe (Step t)

scanPossibleSteps :: [SpecImpProgram t] -> [SpecImpProgram t] -> [PossibleStep t] -> Step t
scanPossibleSteps aprogs eprogs options =
  let steps = catMaybes $ map (\try -> try aprogs eprogs) options
  in case steps of
       []     -> Step NoSelectionFound aprogs eprogs
       step:_ -> step


---------------------
-- Pretty Printing --
---------------------
instance Pretty t => Pretty (Selection t) where
  pretty selection =
    case selection of
      UniversalStatement stmt   -> pretty "Universal:" <+> pretty stmt
      ExistentialStatement stmt -> pretty "Existential:" <+> pretty stmt
      LoopFusion _ _            -> pretty "Loop Fusion"
      NoSelectionFound          -> pretty "No Selection Found"


--------------------------
-- Backward with Fusion --
--------------------------

backwardWithFusion :: BackwardStepStrategy t
backwardWithFusion aprogs eprogs =
  return $ scanPossibleSteps aprogs eprogs [ finished
                                           , stepLoopFusion
                                           , stepExistentialNonLoop
                                           , stepUniversalNonLoop
                                           , stepExistentialAny
                                           , stepUniversalAny
                                           ]

finished :: PossibleStep t
finished [] [] = Just $ Step NoSelectionFound [] []
finished _  _  = Nothing

stepLoopFusion :: PossibleStep t
stepLoopFusion aprogs eprogs =
  let
    alasts  = map lastStatement aprogs
    elasts  = map lastStatement eprogs
    aloops  = catMaybes $ map (getLoop . ls_last) alasts
    eloops  = catMaybes $ map (getLoop . ls_last) elasts
    aprogs' = catMaybes $ map ls_rest alasts
    eprogs' = catMaybes $ map ls_rest elasts
  in
    if      any (not . isLoop . ls_last) alasts then Nothing
    else if any (not . isLoop . ls_last) elasts then Nothing
    else Just $ Step (LoopFusion aloops eloops) aprogs' eprogs'

stepExistentialNonLoop :: PossibleStep t
stepExistentialNonLoop aprogs eprogs =
  let
    lasts = map lastStatement eprogs
    (loops, nonloops) = partition (isLoop . ls_last) lasts
  in case nonloops of
    []     -> Nothing
    (s:ss) ->
      let
        eprogs'NonS = (map ls_full loops) ++ (map ls_full ss)
        eprogs' = case ls_rest s of
                    Nothing -> eprogs'NonS
                    Just r  -> r:eprogs'NonS
      in Just $ Step (ExistentialStatement $ ls_last s) aprogs eprogs'

stepUniversalNonLoop :: PossibleStep t
stepUniversalNonLoop aprogs eprogs =
  let
    lasts = map lastStatement aprogs
    (loops, nonloops) = partition (isLoop . ls_last) lasts
  in case nonloops of
    []     -> Nothing
    (s:ss) ->
      let
        aprogs'NonS = (map ls_full loops) ++ (map ls_full ss)
        aprogs' = case ls_rest s of
                    Nothing -> aprogs'NonS
                    Just r  -> r:aprogs'NonS
      in Just $ Step (UniversalStatement $ ls_last s) aprogs' eprogs

stepExistentialAny :: PossibleStep t
stepExistentialAny aprogs eprogs =
  case map lastStatement eprogs of
    []     -> Nothing
    (s:ss) ->
      let eprogs' = case ls_rest s of
                      Nothing -> map ls_full ss
                      Just r  -> r:(map ls_full ss)
      in Just $ Step (ExistentialStatement $ ls_last s) aprogs eprogs'

stepUniversalAny :: PossibleStep t
stepUniversalAny aprogs eprogs =
  case map lastStatement aprogs of
    []     -> Nothing
    (s:ss) ->
      let aprogs' = case ls_rest s of
                      Nothing -> map ls_full ss
                      Just r  -> r:(map ls_full ss)
      in Just $ Step (UniversalStatement $ ls_last s) aprogs' eprogs



---------------------
-- Last Statements --
---------------------

data LastStatement t = LastStatement { ls_last :: SpecImpProgram t
                                     , ls_rest :: Maybe (SpecImpProgram t)
                                     , ls_full :: SpecImpProgram t
                                     }

singleStatement :: SpecImpProgram t -> LastStatement t
singleStatement stmt = LastStatement stmt Nothing stmt

class FindLastStatement t e where
  lastStatement :: e -> LastStatement t
instance (FindLastStatement t (f e), FindLastStatement t (g e)) => FindLastStatement t ((f :+: g) e) where
  lastStatement (Inl f) = lastStatement f
  lastStatement (Inr g) = lastStatement g
instance FindLastStatement t (SpecImpProgram t) where
  lastStatement (In p) = lastStatement p
instance FindLastStatement t (ImpSkip t e) where
  lastStatement ImpSkip = singleStatement impSkip
instance FindLastStatement t (ImpAsgn t e) where
  lastStatement (ImpAsgn lhs rhs) = singleStatement (impAsgn lhs rhs)
instance FindLastStatement t (ImpSeq t (SpecImpProgram t)) where
  lastStatement (ImpSeq stmts) = case stmts of
    []     -> singleStatement impSkip
    (s:[]) -> singleStatement s
    _      -> let (ss, t) = splitTail stmts
                  LastStatement lastT mRest _ = lastStatement t
              in case mRest of
                   Nothing   -> LastStatement lastT (Just $ impSeq ss) (impSeq stmts)
                   Just rest -> LastStatement lastT (Just $ impSeq $ ss ++ [rest]) (impSeq stmts)
instance FindLastStatement t (ImpIf t (SpecImpProgram t)) where
  lastStatement (ImpIf cond tbranch ebranch) = singleStatement (impIf cond tbranch ebranch)
instance FindLastStatement t (ImpWhile t (SpecImpProgram t)) where
  lastStatement (ImpWhile cond body meta) = singleStatement (impWhileWithMeta cond body meta)
instance FindLastStatement t (SpecCall t (SpecImpProgram t)) where
  lastStatement (SpecCall cid params assignees) = singleStatement (specCall cid params assignees)

splitTail :: [a] -> ([a], a)
splitTail list = case list of
  []     -> error "Empty list"
  (x:[]) -> ([], x)
  (x:xs) -> let (rest, t) = splitTail xs
            in (x:rest, t)


-----------------------------
-- Program Structure Tests --
-----------------------------

class IsSkip e where
  isSkip :: e -> Bool
instance (IsSkip (f e), IsSkip (g e)) => IsSkip ((f :+: g) e) where
  isSkip (Inl f) = isSkip f
  isSkip (Inr g) = isSkip g
instance IsSkip (SpecImpProgram t) where
  isSkip (In p) = isSkip p
instance IsSkip (ImpSkip t e)  where isSkip _ = True
instance IsSkip (ImpAsgn t e)  where isSkip _ = False
instance IsSkip (ImpSeq t e)   where isSkip _ = False
instance IsSkip (ImpIf t e)    where isSkip _ = False
instance IsSkip (ImpWhile t e) where isSkip _ = False
instance IsSkip (ImpCall t e)  where isSkip _ = False
instance IsSkip (SpecCall t e) where isSkip _ = False

isLoop :: forall t. SpecImpProgram t -> Bool
isLoop p = case getLoop @t p of
  Nothing -> False
  Just _  -> True
