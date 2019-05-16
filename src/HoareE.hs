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
    -- TODO: The following corresponds to the ELift rule,
    -- which also says the program must have at least one
    -- terminating state.
    _ -> hlWP stmt post

{-
hleSP :: Cond -> Stmt -> Cond
hleSP pre stmt =
  case stmt of
    -- TODO: Unclear if the following is actually correct.
    Call (UFunc name params fPre fPost) -> CImp
        (CAnd (CImp pre (bexpToCond fPre))
              (CImp abd (bexpToCond fPost)))
        abd
      where abd = CAbducible name params
    -- TODO: The following corresponds to the ELift rule,
    -- which also says the program must have at least one
    -- terminating state.
    _ -> hlSP pre stmt
-}

hleVC :: HLETrip -> Cond
hleVC (HLETrip pre prog post) = CImp pre (hleWP prog post)
