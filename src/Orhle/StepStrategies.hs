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
import Data.List ( partition )
import Data.Maybe ( catMaybes )
import Orhle.SpecImp


type BackwardStepStrategy = [SpecImpProgram] -> [SpecImpProgram] -> Ceili Step

backwardDisallowed :: BackwardStepStrategy
backwardDisallowed _ _ = throwError "Backward stepping not allowed."


-----------
-- Steps --
-----------

data Step = Step { step_selection :: Selection
                 , step_aprogs    :: [SpecImpProgram]
                 , step_eprogs    :: [SpecImpProgram]
                 }

data Selection = UniversalStatement SpecImpProgram
               | ExistentialStatement SpecImpProgram
               | LoopFusion [ImpWhile SpecImpProgram] [ImpWhile SpecImpProgram]
               | NoSelectionFound

type PossibleStep = [SpecImpProgram] -> [SpecImpProgram] -> Maybe Step

scanPossibleSteps :: [SpecImpProgram] -> [SpecImpProgram] -> [PossibleStep] -> Step
scanPossibleSteps aprogs eprogs options =
  let steps = catMaybes $ map (\try -> try aprogs eprogs) options
  in case steps of
       []     -> Step NoSelectionFound aprogs eprogs
       step:_ -> step


--------------------------
-- Backward with Fusion --
--------------------------

backwardWithFusion :: BackwardStepStrategy
backwardWithFusion aprogs eprogs =
  return $ scanPossibleSteps aprogs eprogs [ loopFusion
                                           , stepExistential
                                           , stepUniversal
                                           ]

loopFusion :: PossibleStep
loopFusion aprogs eprogs =
  case partition isLoop aprogs of
    (_, []) -> case partition isLoop eprogs of
                 (_, []) -> Nothing
                 _       -> fusionStep
    _ -> Nothing
  where
    alasts  = map lastStatement aprogs
    elasts  = map lastStatement eprogs
    aloops  = catMaybes $ map (getLoop . ls_last) alasts
    eloops  = catMaybes $ map (getLoop . ls_last) elasts
    aprogs' = catMaybes $ map ls_rest alasts
    eprogs' = catMaybes $ map ls_rest elasts
    fusionStep = Just $ Step (LoopFusion aloops eloops) aprogs' eprogs'

-- Look for a single step on the existential side.
stepExistential :: PossibleStep
stepExistential aprogs eprogs =
  case map lastStatement eprogs of
    []     -> Nothing
    (s:ss) ->
      let eprogs' = case ls_rest s of
                      Nothing -> map ls_full ss
                      Just r  -> r:(map ls_full ss)
      in Just $ Step (ExistentialStatement $ ls_last s) aprogs eprogs'

-- Look for a single step on the universal side.
stepUniversal :: PossibleStep
stepUniversal aprogs eprogs =
  case map lastStatement aprogs of
    []     -> Nothing
    (s:ss) ->
      let aprogs' = case ls_rest s of
                      Nothing -> map ls_full ss
                      Just r  -> r:(map ls_full ss)
      in Just $ Step (ExistentialStatement $ ls_last s) aprogs' eprogs



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
instance FindLastStatement (ImpCall SpecImpProgram) where
  lastStatement (ImpCall cid params assignees) = singleStatement (impCall cid params assignees)
instance FindLastStatement (SpecCall SpecImpProgram) where
  lastStatement (SpecCall cid params assignees) = singleStatement (impSpecCall cid params assignees)

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

class GetLoop e where
  getLoop :: e -> Maybe (ImpWhile SpecImpProgram)
instance (GetLoop (f e), GetLoop (g e)) => GetLoop ((f :+: g) e) where
  getLoop (Inl f) = getLoop f
  getLoop (Inr g) = getLoop g
instance GetLoop SpecImpProgram where
  getLoop (In p) = getLoop p
instance GetLoop (ImpSkip e)  where getLoop _ = Nothing
instance GetLoop (ImpAsgn e)  where getLoop _ = Nothing
instance GetLoop (ImpSeq e)   where getLoop _ = Nothing
instance GetLoop (ImpIf e)    where getLoop _ = Nothing
instance GetLoop (ImpCall e)  where getLoop _ = Nothing
instance GetLoop (SpecCall e) where getLoop _ = Nothing
instance GetLoop (ImpWhile SpecImpProgram) where getLoop = Just

isLoop :: SpecImpProgram -> Bool
isLoop p =
  case getLoop p of
    Nothing -> False
    Just _  -> True
