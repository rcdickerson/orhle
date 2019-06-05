module HoareE
  ( HLETrip(..)
  , hleSP
  ) where

import Conditions
import Imp

data HLETrip = HLETrip
  { hePre :: Cond
  , heProg :: Prog
  , hePost :: Cond
  } deriving (Show)

hleSP :: Cond -> Stmt -> Cond
hleSP pre stmt =
  case stmt of
    Skip        -> pre
    var := aexp -> CAssignPost var aexp pre
    Seq []      -> pre
    Seq (s:ss)  -> hleSP (hleSP pre s) (Seq ss)
    If c s1 s2  -> CAnd (CImp (bexpToCond c) (hleSP pre s1))
                        (CImp (CNot $ bexpToCond c) (hleSP pre s2))
    Call var f  -> CFuncPost var pre (fPostCond f)
