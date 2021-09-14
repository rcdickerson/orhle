module Orhle.CState
  (
  ) where

import Ceili.Assertion
import Ceili.Language.AExp
import Data.Map ( Map )

data CValue = Concrete Integer
            | WithChoice { cv_choiceVars  :: [Name]
                         , cv_constraints :: [Assertion Integer]
                         , cv_value       :: AExp Integer
                         }

type CState = Map Name CValue

class CEval a where
  ceval :: CState -> a -> CValue
