module Verifier where

import Conditions
import Hoare
import HoareE
import Imp
import RHLE
import Z3.Monad

-- TODO
verify :: RHLETrip -> Bool
verify trip@(RHLETrip pre progA progE post) = True
