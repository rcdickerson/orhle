module Hoare
    ( hlSP
    , HLTrip(..)
    , hlVC
    , hlWP
    ) where

import Conditions
import Imp

data HLTrip = HLTrip
  { hPre :: Cond
  , hProg :: Prog
  , hPost :: Cond
  } deriving (Show)

hlWP :: Stmt -> Cond -> Cond
hlWP stmt post =
  case stmt of
    Skip        -> post
    var := aexp -> csubst post var aexp
    Seq []      -> post
    Seq (s:ss)  -> hlWP s (hlWP (Seq ss) post)
    If c s1 s2  -> CAnd (CImp (bexpToCond c) (hlWP s1 post))
                        (CImp (CNot $ bexpToCond c) (hlWP s2 post))
    Call func   -> CAnd (bexpToCond $ preCond func)
                        (CImp (bexpToCond $ postCond func) post)

hlSP :: Cond -> Stmt -> Cond
hlSP pre stmt =
  case stmt of
    Skip        -> pre
    var := aexp -> CAssignPost var aexp pre
    Seq []      -> pre
    Seq (s:ss)  -> hlSP (hlSP pre s) (Seq ss)
    If c s1 s2  -> CAnd (CImp (bexpToCond c) (hlSP pre s1))
                        (CImp (CNot $ bexpToCond c) (hlSP pre s2))
    Call func   -> CImp (CImp pre (bexpToCond $ preCond func))
                        (bexpToCond $ postCond func)

hlVC :: HLTrip -> Cond
hlVC (HLTrip pre prog post) = CImp pre (hlWP prog post)
