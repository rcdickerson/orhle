module RHLE
  ( RHLETrip(..)
  ) where

import Conditions
import Imp

data RHLETrip = RHLETrip
  { rhlePre :: Cond
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost :: Cond
  } deriving (Show)
