{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
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

type BackwardStepStrategy = [SpecImpProgram] -> [SpecImpProgram] -> Ceili Step

backwardDisallowed :: BackwardStepStrategy
backwardDisallowed _ _ = throwError "Backward stepping not allowed."


-----------
-- Steps --
-----------

data Step = Step { step_selection :: Selection
                 , step_aprogs    :: [SpecImpProgram]
                 , step_eprogs    :: [SpecImpProgram]
                 } deriving (Show, Eq)

data Selection = UniversalStatement SpecImpProgram
               | ExistentialStatement SpecImpProgram
               | LoopFusion [ImpWhile SpecImpProgram] [ImpWhile SpecImpProgram]
               | NoSelectionFound
               deriving (Show, Eq)

type PossibleStep = [SpecImpProgram] -> [SpecImpProgram] -> Maybe Step

scanPossibleSteps :: [SpecImpProgram] -> [SpecImpProgram] -> [PossibleStep] -> Step
scanPossibleSteps aprogs eprogs options =
  let steps = catMaybes $ map (\try -> try aprogs eprogs) options
  in case steps of
       []     -> Step NoSelectionFound aprogs eprogs
       step:_ -> step


---------------------
-- Pretty Printing --
---------------------
instance Pretty Selection where
  pretty selection =
    case selection of
      UniversalStatement stmt   -> pretty "Universal:" <+> pretty stmt
      ExistentialStatement stmt -> pretty "Existential:" <+> pretty stmt
      LoopFusion _ _            -> pretty "Loop Fusion"
      NoSelectionFound          -> pretty "No Selection Found"


--------------------------
-- Backward with Fusion --
--------------------------

backwardWithFusion :: BackwardStepStrategy
backwardWithFusion aprogs eprogs =
  return $ scanPossibleSteps aprogs eprogs [ finished
                                           , stepLoopFusion
                                           , stepExistentialNonLoop
                                           , stepUniversalNonLoop
                                           , stepExistentialAny
                                           , stepUniversalAny
                                           ]

finished :: PossibleStep
finished [] [] = Just $ Step NoSelectionFound [] []
finished _  _  = Nothing

stepLoopFusion :: PossibleStep
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

stepExistentialNonLoop :: PossibleStep
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

stepUniversalNonLoop :: PossibleStep
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

stepExistentialAny :: PossibleStep
stepExistentialAny aprogs eprogs =
  case map lastStatement eprogs of
    []     -> Nothing
    (s:ss) ->
      let eprogs' = case ls_rest s of
                      Nothing -> map ls_full ss
                      Just r  -> r:(map ls_full ss)
      in Just $ Step (ExistentialStatement $ ls_last s) aprogs eprogs'

stepUniversalAny :: PossibleStep
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

data LastStatement = LastStatement { ls_last :: SpecImpProgram
                                   , ls_rest :: Maybe SpecImpProgram
                                   , ls_full :: SpecImpProgram
                                   }

singleStatement :: SpecImpProgram -> LastStatement
singleStatement stmt = LastStatement stmt Nothing stmt

class FindLastStatement e where
  lastStatement :: e -> LastStatement
instance (FindLastStatement (f e), FindLastStatement (g e)) => FindLastStatement ((f :+: g) e) where
  lastStatement (Inl f) = lastStatement f
  lastStatement (Inr g) = lastStatement g
instance FindLastStatement SpecImpProgram where
  lastStatement (In p) = lastStatement p
instance FindLastStatement (ImpSkip e) where
  lastStatement ImpSkip = singleStatement impSkip
instance FindLastStatement (ImpAsgn e) where
  lastStatement (ImpAsgn lhs rhs) = singleStatement (impAsgn lhs rhs)
instance FindLastStatement (ImpSeq SpecImpProgram) where
  lastStatement (ImpSeq stmts) = case stmts of
    []     -> singleStatement impSkip
    (s:[]) -> singleStatement s
    _      -> let (ss, t) = splitTail stmts
                  LastStatement lastT mRest _ = lastStatement t
              in case mRest of
                   Nothing   -> LastStatement lastT (Just $ impSeq ss) (impSeq stmts)
                   Just rest -> LastStatement lastT (Just $ impSeq $ ss ++ [rest]) (impSeq stmts)
instance FindLastStatement (ImpIf SpecImpProgram) where
  lastStatement (ImpIf c t e) = singleStatement (impIf c t e)
instance FindLastStatement (ImpWhile SpecImpProgram) where
  lastStatement (ImpWhile c body meta) = singleStatement (impWhileWithMeta c body meta)
instance FindLastStatement (SpecCall SpecImpProgram) where
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
instance IsSkip SpecImpProgram where
  isSkip (In p) = isSkip p
instance IsSkip (ImpSkip e)  where isSkip _ = True
instance IsSkip (ImpAsgn e)  where isSkip _ = False
instance IsSkip (ImpSeq e)   where isSkip _ = False
instance IsSkip (ImpIf e)    where isSkip _ = False
instance IsSkip (ImpWhile e) where isSkip _ = False
instance IsSkip (ImpCall e)  where isSkip _ = False
instance IsSkip (SpecCall e) where isSkip _ = False

isLoop :: SpecImpProgram -> Bool
isLoop p = case getLoop p of
  Nothing -> False
  Just _  -> True
