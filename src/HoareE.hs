module HoareE where

import Conditions
import Hoare
import Imp

data HLETrip = HLETrip
  { hePre :: Cond
  , heProg :: Prog
  , hePost :: Cond
  } deriving (Show)

hleWP :: Stmt -> Cond -> Cond
hleWP stmt post =
  case stmt of
    Call func -> CAnd (CImp post (bexpToCond $ postCond func))
                      (bexpToCond $ preCond func)
    -- The following corresponds to the ELift rule, which also
    -- says the program must have at least one terminating state.
    -- In our current IMP definition, all programs terminate, but
    -- if that ever changes we will need to add some sort of
    -- termination condition here.
    _ -> hlWP stmt post

hleVC :: HLETrip -> Cond
hleVC (HLETrip pre prog post) = CImp pre (hleWP prog post)
