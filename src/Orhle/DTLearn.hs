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
import Data.Maybe ( catMaybes )
import Data.Set ( Set, (\\) )
import qualified Data.Set as Set
import Data.Map ( Map )
import qualified Data.Map as Map
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
  let startingAtSize size = do
        log_d $ "[DTLearn] Examining features of size " ++ show size
        eliminations <- rankEliminations (Set.fromList badStates) (features size)
        log_d $ "[DTLearn] " ++ show (countEliminations eliminations) ++ " features which eliminate at least one bad state."
        mResult <- learnSeparator' eliminations (Set.fromList badStates) (Set.fromList goodStates)
        case mResult of
          Nothing -> if (size >= maxFeatureSize)
                     then do (log_d $ "[DTLearn] Unable to find any separator within features of size " ++ show maxFeatureSize)
                               >> return Nothing
                     else startingAtSize (size + 1)
          Just result -> do
            log_d $ "[DTLearn] Learned separator: " ++ show result
            return mResult
  startingAtSize maxFeatureSize --startingAtSize 1

learnSeparator' :: ( Ord t
                   , StatePredicate (Assertion t) t
                   , SatCheckable t
                   , Pretty t
                   )
                => RankedEliminations t
                -> Set (ProgState t)
                -> Set (ProgState t)
                -> Ceili (Maybe (Assertion t))
learnSeparator' eliminations badStates goodStates = do
  log_d $ "[DTLearn] Learning clause..."
  clauseResult <- learnClause eliminations badStates goodStates (Set.empty)
  case clauseResult of
    Nothing -> return Nothing
    Just lc@(LearnedClause lcElims allowedGoods) -> do
      let clause = aAnd $ Set.toList (lc_conjuncts lc)
      let remainingGoods = goodStates \\ allowedGoods
      if Set.null remainingGoods
        then return . Just $ clause
        else do
          let eliminations' = removeEliminations lcElims eliminations -- No more bad states will be removed by these conjuncts.
          separator' <- learnSeparator' eliminations' badStates remainingGoods
          return $ case separator' of
            Nothing   -> Nothing
            Just rest -> Just $ aOr [clause, rest]


---------------------
-- Clause Learning --
---------------------

data LearnedClause t =
  LearnedClause { lc_eliminations :: Set (Elimination t)
                , lc_allowedGood  :: Set (ProgState t)
                }

lc_conjuncts :: Ord t => LearnedClause t -> Set (Assertion t)
lc_conjuncts = (Set.map elim_feature) . lc_eliminations

learnClause :: ( Ord t
               , StatePredicate (Assertion t) t
               , SatCheckable t
               , Pretty t
               )
            => RankedEliminations t
            -> Set (ProgState t)
            -> Set (ProgState t)
            -> Set (Elimination t)
            -> Ceili (Maybe (LearnedClause t))
learnClause eliminations badStates goodStates selected = do
  -- log_d . show $ pretty "[DTLearn]   bad states: "  <+> (align . prettyProgStates . Set.toList) badStates
  -- log_d . show $ pretty "[DTLearn]   good states: " <+> (align . prettyProgStates . Set.toList) goodStates
  let currentConj = elimSetToClause selected
  allowedGood <- statesMeeting currentConj goodStates
  if Set.null allowedGood then
    return Nothing
  else if Set.null badStates then
    return . Just $ LearnedClause selected allowedGood
  else
    scanEliminations eliminations badStates allowedGood selected

scanEliminations :: ( Ord t
                    , StatePredicate (Assertion t) t
                    , SatCheckable t
                    , Pretty t
                    )
                 => RankedEliminations t
                 -> Set (ProgState t)
                 -> Set (ProgState t)
                 -> Set (Elimination t)
                 -> Ceili (Maybe (LearnedClause t))
scanEliminations elims badStates goodStates selected =
  if Map.null elims
  then return Nothing
  else do
    let (selectedElim, elims') = popElimination elims
    let remainingBad = Set.intersection badStates (elim_remainingBadStates selectedElim)
    let selected' = Set.insert selectedElim selected
    allowedGood <- statesMeeting (elimSetToClause selected') goodStates
    if Set.null allowedGood then
      -- This choice eliminates all the good states. Keep moving down the list.
      scanEliminations elims' badStates goodStates selected
    else if Set.null remainingBad then do
      -- We got rid of all the bad states while allowing some good states. Hooray!
      log_d $ "[DTLearn] Learned clause: " ++ show (elimSetToClause selected')
      return . Just $ LearnedClause selected' allowedGood
    else do
      -- We got rid of some bad states while keeping some good states.
      -- However, there are still some bad states left. Try adding more conjuncts.
      result <- learnClause elims' remainingBad allowedGood selected'
      case result of
        Nothing -> scanEliminations elims' badStates goodStates selected -- Didn't work, backtrack.
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
              } deriving (Eq, Ord)

elimSetToClause :: Set (Elimination t) -> Assertion t
elimSetToClause elimSet =
  if Set.null elimSet
  then ATrue
  else aAnd . (map elim_feature) . Set.toList $ elimSet

-- The lower the rank, the better.
type RankedEliminations t = Map Int (Set (Elimination t))

rankEliminations :: ( Ord t
                    , StatePredicate (Assertion t) t
                    )
                 => Set (ProgState t)
                 -> Set (Assertion t)
                 -> Ceili (RankedEliminations t)
rankEliminations badStates assertions = do
  let evalElim assertion = do
        remainingBadStates <- statesMeeting assertion badStates
        let remainingBadCount = Set.size remainingBadStates
        if remainingBadCount == Set.size badStates
          then return Nothing
          else return . Just $ (remainingBadCount, Elimination assertion remainingBadStates)
  eliminations <- sequence $ map evalElim (Set.toList assertions)
  let insertElim (rank, elim) elimMap = let
        rset = Map.findWithDefault Set.empty rank elimMap
        rset' = Set.insert elim rset
        in Map.insert rank rset' elimMap
  return $ foldr insertElim Map.empty (catMaybes eliminations)

popElimination :: RankedEliminations t -> (Elimination t, RankedEliminations t)
popElimination elims =
  let
    (rank, rset)    = Map.findMin elims
    (result, rset') = Set.deleteFindMin rset
    elims'          = if Set.null rset'
                      then Map.delete rank elims
                      else Map.insert rank rset' elims
  in (result, elims')

removeEliminations :: Ord t => Set (Elimination t) -> RankedEliminations t -> RankedEliminations t
removeEliminations vals = Map.map (\\ vals)

countEliminations :: RankedEliminations t -> Int
countEliminations elimMap =
  let counts = map (Set.size) $ Map.elems elimMap
  in foldr (+) 0 counts
