module Orhle.DTLearn
  ( learnSeparator
  ) where

import Ceili.Assertion
import Ceili.CeiliEnv
import Ceili.Evaluation
import Ceili.ProgState
import Control.Monad ( filterM )
import Data.Set ( Set, (\\) )
import qualified Data.Set as Set
import Orhle.CValue


learnSeparator :: Set (ProgState CValue)
               -> Set (ProgState CValue)
               -> Set (Assertion Integer)
               -> Ceili (Maybe (Assertion Integer))
learnSeparator goodStates badStates features = do
  candidates <- return . Set.fromList =<< filterM (satisfiesAll $ Set.toList goodStates) (Set.toList features)
  learnSeparator' goodStates badStates candidates

learnSeparator' :: Set (ProgState CValue)
                -> Set (ProgState CValue)
                -> Set (Assertion Integer)
                -> Ceili (Maybe (Assertion Integer))
learnSeparator' goodStates badStates features = do
  clauseResult <- learnClause goodStates badStates features Set.empty
  case clauseResult of
    Nothing -> return Nothing
    Just (LearnedClause conjuncts allowedGoods) -> do
      let clause = aAnd $ Set.toList conjuncts
      let remainingGoods = goodStates \\ allowedGoods
      if Set.null remainingGoods
        then return . Just $ clause
        else do
          let features' = features \\ conjuncts
          separator' <- learnSeparator remainingGoods badStates features'
          return $ case separator' of
            Nothing   -> Nothing
            Just rest -> Just $ aAnd [clause, rest]

satisfiesAll :: [ProgState CValue]
             -> Assertion Integer
             -> Ceili Bool
satisfiesAll states assertion = case states of
  [] -> return True
  state:rest -> do
    steval <- eval () state (fmap Concrete assertion)
    case steval of
      False -> return False
      True  -> satisfiesAll rest assertion


---------------------
-- Clause Learning --
---------------------

data LearnedClause =
  LearnedClause { lc_conjuncts   :: Set (Assertion Integer)
                , lc_allowedGood :: Set (ProgState CValue)
                }

learnClause :: Set (ProgState CValue)
            -> Set (ProgState CValue)
            -> Set (Assertion Integer)
            -> Set (Assertion Integer)
            -> Ceili (Maybe LearnedClause)
learnClause goodStates badStates candidates selected =
  if Set.null badStates
    then return . Just $ LearnedClause selected goodStates
    else do
      eliminations <- rankEliminations badStates candidates
      result <- scanEliminations eliminations goodStates candidates selected
      return $ case result of
        Nothing -> Nothing
        Just (features, allowedGoods) ->
          Just $ LearnedClause features allowedGoods

scanEliminations :: [Elimination]
                 -> Set (ProgState CValue)
                 -> Set (Assertion Integer)
                 -> Set (Assertion Integer)
                 -> Ceili ( Maybe ( Set (Assertion Integer)
                                  , Set (ProgState CValue)))
scanEliminations elims goodStates candidates selected = case elims of
  [] -> return Nothing
  (Elimination feature remainingBad):rest -> do
    let selected' = Set.insert feature selected
    allowedGood <- statesMeeting (aAnd $ Set.toList selected') goodStates
    if Set.null allowedGood then
      -- This choice eliminates all the good states. Keep moving down the list.
      scanEliminations rest goodStates candidates selected
    else if Set.null remainingBad then
      -- We got rid of all the bad states while allowing some good states. Hooray!
      return . Just $ (selected', allowedGood)
    else do
      -- We got rid of some bad states while keeping some good states.
      -- However, there are still some bad states left. Try adding more conjuncts.
      let features' = Set.delete feature candidates
      result <- learnClause goodStates remainingBad features' selected'
      case result of
        Nothing -> scanEliminations rest goodStates candidates selected -- Didn't work, backtrack.
        Just (LearnedClause features allowedGoods) ->
          return . Just $ (Set.insert feature features, allowedGoods)

statesMeeting :: Assertion Integer
              -> Set (ProgState CValue)
              -> Ceili (Set (ProgState CValue))
statesMeeting assertion states = do
  let cvAssertion = fmap Concrete assertion
  let assertionsAtStates = Set.map (\s -> assertionAtState s cvAssertion) states
--  sequence $ map verifyCAssertion (Set.toList assertionsAtStates)
  error "unimplemented"


------------------
-- Eliminations --
------------------

data Elimination =
  Elimination { elim_feature           :: Assertion Integer
              , elim_remainingStates   :: Set (ProgState CValue)
              }

rankEliminations :: Set (ProgState CValue)
                 -> Set (Assertion Integer)
                 -> Ceili [Elimination]
rankEliminations = error "unimplemented"
