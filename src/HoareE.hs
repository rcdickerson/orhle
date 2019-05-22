module HoareE
  ( HLETrip(..)
  , hleSP
  , hleVC
  , hleWP
  ) where

import Conditions
import Hoare
import Imp

data HLETrip = HLETrip
  { hePre :: Cond
  , heProg :: Prog
  , hePost :: Cond
  } deriving (Show)

hleWP :: Stmt -> Cond -> Cond
hleWP (Call func) post =
  CAnd (CImp post (bexpToCond $ postCond func))
       (bexpToCond $ preCond func)
hleWP stmt post = hlWP stmt post

hleSP :: Cond -> Stmt -> Cond
hleSP pre (Call (UFunc fName fParams fPre fPost)) =
  CAnd pre (CImp (bexpToCond fPre) (bexpToCond fPost))
hleSP pre stmt = hlSP pre stmt

hleVC :: HLETrip -> Cond
hleVC (HLETrip pre prog post) =
  CImp pre (hleWP prog post)
