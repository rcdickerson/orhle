module HoareE
  ( HLETrip(..)
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

hleVC :: HLETrip -> Cond
hleVC (HLETrip pre prog post) =
  CImp pre (hleWP prog post)
