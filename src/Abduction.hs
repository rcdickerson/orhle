module Abduction
    ( abduce
    ) where

import Conditions
import Imp
import Z3.Monad

abduce :: Cond -> Cond -> Cond
abduce chi post = post -- TODO
