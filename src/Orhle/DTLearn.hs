{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Orhle.DTLearn
  ( learnSeparator
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.ProgState
import Ceili.StatePredicate
import Control.Monad ( filterM )
import Data.List ( sortOn )
import Data.Maybe ( catMaybes )
import Data.Set ( Set, (\\) )
import qualified Data.Set as Set
import Prettyprinter

-- Learning a DNF formula, a disjunction of clauses.
-- Each clause is a conjunction of candidate features.
-- Each clause must rule out *all* bad states.
-- Each clause must allow at least one good state or it can be safely omitted.
-- Every good state must be allowed by *at least one* clause.

learnSeparator :: ( Ord t
                  , StatePredicate (Assertion t) t
                  , SatCheckable t
                  , Pretty t
                  )
               => Int
               -> (Int -> Set (Assertion t))
               -> [ProgState t]
               -> [ProgState t]
               -> Ceili (Maybe (Assertion t))
learnSeparator maxFeatureSize features badStates goodStates = do
  let interestingFeature = eliminatesAtLeastOne badStates
  let startingAtSize size = do
        log_d $ "[DTLearn] Examining features of size " ++ show size
        candidates <- return . Set.fromList =<< filterM interestingFeature (Set.toList $ features size)
        log_d $ "[DTLearn] " ++ show (Set.size candidates) ++ " features which eliminate at least one bad state."
        mResult <- learnSeparator' candidates (Set.fromList badStates) (Set.fromList goodStates)
        case mResult of
          Nothing -> if (size >= maxFeatureSize)
                     then do (log_d $ "[DTLearn] Unable to find any separator within features of size " ++ show maxFeatureSize)
                               >> return Nothing
                     else startingAtSize (size + 1)
          Just result -> do
            log_d $ "[DTLearn] Learned separator: " ++ show result
            return mResult
  startingAtSize 1

learnSeparator' :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , SatCheckable t
                   , Pretty t
                   )
                => Set (Assertion t)
                -> Set (ProgState t)
                -> Set (ProgState t)
                -> Ceili (Maybe (Assertion t))
learnSeparator' features badStates goodStates = do
  clauseResult <- learnClause badStates goodStates features (Set.singleton ATrue)
  case clauseResult of
    Nothing -> return Nothing
    Just (LearnedClause conjuncts allowedGoods) -> do
      let clause = aAnd $ Set.toList conjuncts
      let remainingGoods = goodStates \\ allowedGoods
      if Set.null remainingGoods
        then return . Just $ clause
        else do
          let features' = features \\ conjuncts
          separator' <- learnSeparator' features' badStates remainingGoods
          return $ case separator' of
            Nothing   -> Nothing
            Just rest -> Just $ aOr [clause, rest]

eliminatesAtLeastOne :: StatePredicate (Assertion t) t
                     => [ProgState t]
                     -> Assertion t
                     -> Ceili Bool
eliminatesAtLeastOne states assertion = case states of
  [] -> return False
  state:rest -> do
    steval <- testState assertion state
    case steval of
      False -> return True
      True  -> eliminatesAtLeastOne rest assertion


---------------------
-- Clause Learning --
---------------------

data LearnedClause t =
  LearnedClause { lc_conjuncts   :: Set (Assertion t)
                , lc_allowedGood :: Set (ProgState t)
                }

learnClause :: ( Ord t
               , StatePredicate (Assertion t) t
               , SatCheckable t
               , Pretty t
               )
            => Set (ProgState t)
            -> Set (ProgState t)
            -> Set (Assertion t)
            -> Set (Assertion t)
            -> Ceili (Maybe (LearnedClause t))
learnClause badStates goodStates candidates selected = do
  log_d $ "[DTLearn] Learning clause..."
  log_d . show $ pretty "[DTLearn]   bad states: "  <+> (align . prettyProgStates . Set.toList) badStates
  -- log_d . show $ pretty "[DTLearn]   good states: " <+> (align . prettyProgStates . Set.toList) goodStates
  allowedGood <- statesMeeting (aAnd $ Set.toList selected) goodStates
  if Set.null allowedGood
    then return Nothing
  else if Set.null badStates
    then return . Just $ LearnedClause selected allowedGood
    else do
      eliminations <- rankEliminations badStates candidates
      scanEliminations eliminations allowedGood candidates selected

scanEliminations :: ( Ord t
                    , StatePredicate (Assertion t) t
                    , SatCheckable t
                    , Pretty t
                    )
                 => [Elimination t]
                 -> Set (ProgState t)
                 -> Set (Assertion t)
                 -> Set (Assertion t)
                 -> Ceili (Maybe (LearnedClause t))
scanEliminations elims goodStates candidates selected = case elims of
  [] -> do
    log_d "[DTLearn] No features left to consider."
    return Nothing
  (Elimination feature remainingBad):rest -> do
    let selected' = Set.insert feature selected
--    selectionSat <- checkSatB $ aAnd (Set.toList selected')
    allowedGood <- statesMeeting (aAnd $ Set.toList selected') goodStates
--    if not selectionSat then
      -- This choice is incompatible with the current selection. Keep moving down the list.
--      scanEliminations rest goodStates candidates selected
    if Set.null allowedGood then
      -- This choice eliminates all the good states. Keep moving down the list.
      scanEliminations rest goodStates candidates selected
    else if Set.null remainingBad then do
      -- We got rid of all the bad states while allowing some good states. Hooray!
      log_d $ "[DTLearn] Learned clause: " ++ show selected'
      return . Just $ LearnedClause selected' allowedGood
    else do
      -- We got rid of some bad states while keeping some good states.
      -- However, there are still some bad states left. Try adding more conjuncts.
      let features' = Set.delete feature candidates
      result <- learnClause remainingBad allowedGood features' selected'
      case result of
        Nothing -> scanEliminations rest goodStates candidates selected -- Didn't work, backtrack.
        Just _  -> return result -- We found a solution.

statesMeeting :: forall t.
                 ( Ord t
                 , StatePredicate (Assertion t) t
                 )
              => Assertion t
              -> Set (ProgState t)
              -> Ceili (Set (ProgState t))
statesMeeting assertion states = do
  let resultPairs state = do result <- testState assertion state; return (state, result)
  evaluations <- sequence $ map resultPairs (Set.toList states)
  let statesList = (map fst) . (filter snd) $ evaluations
  return $ Set.fromList statesList


------------------
-- Eliminations --
------------------

data Elimination t =
  Elimination { elim_feature            :: Assertion t
              , elim_remainingBadStates :: Set (ProgState t)
              }

rankEliminations :: ( Ord t
                    , StatePredicate (Assertion t) t
                    )
                 => Set (ProgState t)
                 -> Set (Assertion t)
                 -> Ceili [Elimination t]
rankEliminations badStates assertions = do
  let evalElim assertion = do
        remainingBadStates <- statesMeeting assertion badStates
        if Set.size remainingBadStates == Set.size badStates
          then return Nothing
          else return . Just $ Elimination assertion remainingBadStates
  eliminations <- sequence $ map evalElim (Set.toList assertions)
  return $ sortOn (Set.size . elim_remainingBadStates) (catMaybes eliminations)
