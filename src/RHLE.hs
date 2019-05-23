module RHLE
  ( rhleEncode
  , RHLETrip(..)
  ) where

import Abduction
import Conditions
import Hoare
import HoareE
import Imp

data RHLETrip = RHLETrip
  { rhlePre :: Cond
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost :: Cond
  } deriving (Show)
