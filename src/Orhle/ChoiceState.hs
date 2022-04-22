module Orhle.ChoiceState
  ( ChoiceState(..)
  , ChoiceStrategy(..)
  , reifyChoices
  ) where

import Ceili.Assertion
import Ceili.ProgState
import qualified Data.Map as Map

data ChoiceState t = ChoiceState
  { cstAbstractState  :: ProgState (Arith t)
  , cstDependantState :: ChoiceState t
  }

data ChoiceStrategy t a = ChoiceStrategy
  { csrVariable :: Name
  , csrStrategy :: ProgState a -> a
  }

reifyChoices :: [ChoiceStrategy t a] -> ChoiceState t -> ProgState a
reifyChoices strategies (ChoiceState absState depState) =
  let
    reifiedDep = reifyChoices strategies depState
    makeChoice (ChoiceStrategy var strat) = (var, strat reifiedDep)
    choices = map makeChoice strategies
  in error "" --Map.map (strategy reifiedDep) absState
