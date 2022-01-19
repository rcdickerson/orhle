{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Orhle.DTLearn
  ( learnSeparator
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Embedding
import Ceili.Name
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

learnSeparator :: ( Embeddable Integer t
                  , Ord t
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
  if null badStates
    then pure $ Just ATrue
    else do
      --startAtSize 1 maxFeatureSize features badStates goodStates
      startAtSize maxFeatureSize maxFeatureSize features badStates goodStates


startAtSize :: ( Embeddable Integer t
               , Ord t
               , StatePredicate (Assertion t) t
               , SatCheckable t
               , Pretty t
               )
               => Int
               -> Int
               -> (Int -> Set (Assertion t))
               -> [ProgState t]
               -> [ProgState t]
               -> Ceili (Maybe (Assertion t))
startAtSize currentSize maxSize featureGen rawBadStates rawGoodStates = do
  log_d $ "[DTLearn] Examining features of size " ++ show currentSize
  let features = featureGen currentSize
  -- Add missing names to states. TODO: This might not be the best place for this.
  let allNames = Set.unions $ (Set.toList $ Set.map namesIn features)
                            ++ map namesIn rawBadStates
                            ++ map namesIn rawGoodStates
  let prepareStates = Set.fromList . (map $ addMissingNames (Set.toList allNames))
  let badStates = prepareStates rawBadStates
  let goodStates = prepareStates rawGoodStates
  -------
  eliminations <- rankEliminations badStates (featureGen currentSize)
  -- log_d . show $ pretty "***** Eliminations: " <+> pretty eliminations
  log_d $ "[DTLearn] " ++ show (countEliminations eliminations) ++ " features which eliminate at least one bad state."
  mResult <- learnSeparator' eliminations badStates goodStates
  case mResult of
    Nothing -> if (currentSize >= maxSize)
               then do (log_d $ "[DTLearn] Unable to find any separator within features of size " ++ show maxSize)
                         >> pure Nothing
               else startAtSize (currentSize + 1) maxSize featureGen rawBadStates rawGoodStates
    Just result -> do
      log_d $ "[DTLearn] Learned separator: " ++ show result
      pure mResult

addMissingNames :: forall t. (Ord t, Embeddable Integer t) => [Name] -> ProgState t -> ProgState t
addMissingNames names progState = foldr
                                  (\name st -> if Map.member name st
                                    then st
                                    else Map.insert name (embed 0) st)
                                  progState names

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
  clauseResult <- learnClause eliminations badStates goodStates Set.empty
  case clauseResult of
    Nothing -> pure Nothing
    Just lc@(LearnedClause lcElims allowedGoods) -> do
      let clause = aAnd $ Set.toList (lc_conjuncts lc)
      log_d $ "[DTLearn] Found clause: " ++ show clause
      let remainingGoods = goodStates \\ allowedGoods
      if Set.null remainingGoods
        then pure . Just $ clause
        else do
          let eliminations' = removeEliminations lcElims eliminations -- No more bad states will be removed by these conjuncts.
          separator' <- learnSeparator' eliminations' badStates remainingGoods
          pure $ case separator' of
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
  --log_d . show $ pretty "[DTLearn]   bad states: "  <+> (align . prettyProgStates . Set.toList) badStates
  --log_d . show $ pretty "[DTLearn]   good states: " <+> (align . prettyProgStates . Set.toList) goodStates
  if Set.null selected
    then scanEliminations eliminations badStates goodStates selected
    else do
      let currentConj = elimSetToClause selected
      log_d $ "[DTLearn]   selected clauses: " ++ show currentConj
      allowedGood <- statesMeeting currentConj goodStates
      log_d $ "[DTLearn]   allowed good count: " ++ show (Set.size allowedGood)
      -- log_d . show $ pretty "[DTLearn]   allowed good: "  <+> (align . prettyProgStates . Set.toList) allowedGood
      if Set.null allowedGood then
        pure Nothing
      else if Set.null badStates then
        pure . Just $ LearnedClause selected allowedGood
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
  then pure Nothing
  else do
    let (selectedElim, elims') = popElimination elims
    -- log_d . show $ pretty "***** Bad states: " <+> (align . prettyProgStates . Set.toList) badStates
    -- log_d . show $ pretty "***** Remaining bad states: " <+> (align . prettyProgStates . Set.toList) (elim_remainingBadStates selectedElim)
    let remainingBad = Set.intersection badStates (elim_remainingBadStates selectedElim)
    let selected' = Set.insert selectedElim selected
    -- log_d $ "*****Selected: " ++ show (elimSetToClause selected')
    allowedGood <- statesMeeting (elimSetToClause selected') goodStates
    if Set.null allowedGood then do
      -- This choice eliminates all the good states. Keep moving down the list.
      -- log_d $ "****Eliminates all good"
      -- log_d $ "****Good states: " ++ (show . align . prettyProgStates . Set.toList) goodStates
      scanEliminations elims' badStates goodStates selected
    else if Set.null remainingBad then do
      -- We got rid of all the bad states while allowing some good states. Hooray!
      log_d $ "[DTLearn] Learned clause: " ++ show (elimSetToClause selected')
      pure . Just $ LearnedClause selected' allowedGood
    else do
      -- We got rid of some bad states while keeping some good states.
      -- However, there are still some bad states left. Try adding more conjuncts.
      -- log_d $ "****Some bad left"
      result <- learnClause elims' remainingBad allowedGood selected'
      case result of
        Nothing -> scanEliminations elims' badStates goodStates selected -- Didn't work, backtrack.
        Just _  -> pure result -- We found a solution.

statesMeeting :: forall t.
                 ( Ord t
                 , StatePredicate (Assertion t) t
                 )
              => Assertion t
              -> Set (ProgState t)
              -> Ceili (Set (ProgState t))
statesMeeting assertion states = do
  let resultPairs state = do result <- testState assertion state; pure (state, result)
  evaluations <- sequence $ map resultPairs (Set.toList states)
  let statesList = (map fst) . (filter snd) $ evaluations
  pure $ Set.fromList statesList


------------------
-- Eliminations --
------------------

data Elimination t =
  Elimination { elim_feature            :: Assertion t
              , elim_remainingBadStates :: Set (ProgState t)
              } deriving (Show, Eq, Ord)

instance Pretty t => Pretty (Elimination t) where
  pretty (Elimination feature remainingBad) =
        pretty "Elimination: "
    <+> pretty feature
    <>  pretty ", remaining bad: "
    <+> (align . prettyProgStates . Set.toList) remainingBad

instance CollectableNames (Elimination t) where
  namesIn (Elimination feature remBad) = Set.union (namesIn feature) (namesIn $ Set.toList remBad)

elimSetToClause :: Set (Elimination t) -> Assertion t
elimSetToClause elimSet =
  if Set.null elimSet
  then ATrue
  else aAnd . (map elim_feature) . Set.toList $ elimSet

-- The lower the rank, the better.
type RankedEliminations t = Map Int (Set (Elimination t))

instance Pretty t => Pretty (RankedEliminations t) where
  pretty elims = align . pretty . (map Set.toList) $ Map.elems elims

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
          then pure Nothing
          else pure . Just $ (remainingBadCount, Elimination assertion remainingBadStates)
  eliminations <- sequence $ map evalElim (Set.toList assertions)
  let insertElim (rank, elim) elimMap = let
        rset = Map.findWithDefault Set.empty rank elimMap
        rset' = Set.insert elim rset
        in Map.insert rank rset' elimMap
  pure $ foldr insertElim Map.empty (catMaybes eliminations)

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
