module RHLE where

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

rhleVCs :: RHLETrip -> [Cond]
rhleVCs trip =
  case (rhleProgA trip) of
    Skip -> stepR trip
    _    -> stepL trip

stepL :: RHLETrip -> [Cond]
stepL (RHLETrip pre progA progE post) =
  case progA of
    Skip          -> rhleVCs $ RHLETrip pre Skip progE post
    Seq []        -> rhleVCs $ RHLETrip pre Skip progE post
    Seq (s:ss)    -> rhleVCs $ RHLETrip (hlSP pre s) (Seq ss) progE post
    var := aexp   -> rhleVCs $ RHLETrip (hlSP pre (var := aexp)) Skip progE post
    If bexp s1 s2 -> (rhleVCs $ RHLETrip (CAnd pre c) s1 progE post)
                  ++ (rhleVCs $ RHLETrip (CAnd pre (CNot c)) s2 progE post)
                     where c = bexpToCond bexp
    Call func     -> rhleVCs $ RHLETrip (hlSP pre (Call func)) Skip progE post

stepR :: RHLETrip -> [Cond]
stepR (RHLETrip pre progA progE post) =
  case progE of
    Skip          -> [CImp pre post]
    Seq []        -> [CImp pre post]
    Seq (s:ss)    -> rhleVCs $ RHLETrip (hleSP pre s) progA (Seq ss) post
    var := aexp   -> rhleVCs $ RHLETrip (hleSP pre (var := aexp)) progA Skip post
    If bexp s1 s2 -> (rhleVCs $ RHLETrip (CAnd pre c) progA s1 post)
                  ++ (rhleVCs $ RHLETrip (CAnd pre (CNot c)) progA s2 post)
                     where c = bexpToCond bexp
    Call func     -> rhleVCs $ RHLETrip (hlSP pre (Call func)) progA Skip post
