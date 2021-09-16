module Orhle.CState
  ( CValue(..)
  ) where

import Ceili.Assertion
import Ceili.Language.AExp

data CValue = Concrete Integer
            | WithChoice { cv_choiceVars  :: [Name]
                         , cv_constraints :: [Assertion Integer]
                         , cv_value       :: AExp Integer
                         }
