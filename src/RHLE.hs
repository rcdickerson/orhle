module RHLE
  ( rhleVCs
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
    Call (UFunc fName fParams fPre fPost)
                  -> [ CImp pre (bexpToCond fPre)
                     , CImp (bexpToCond fPost) post]

-- Note: This function assumes progA is SKIP.
-- If this assumption changes, this method will need to be updated.
-- All lines that make this assumption are explicitly noted.
stepR :: RHLETrip -> [Cond]
stepR (RHLETrip pre progA@Skip progE post) =
  case progE of
    Skip          -> [CImp pre post] -- Assumes progA is SKIP
    var := aexp   -> rhleVCs $ RHLETrip (hlSP pre (var := aexp)) progA Skip post
    Seq []        -> [CImp pre post] -- Assumes progA is SKIP
    Seq ((Call (UFunc fName fParams fPre fPost)):ss)
                  -> (CAnd pre (bexpToCond fPre))
                   : (CImp abd (bexpToCond fPost))
                   : (rhleVCs $ RHLETrip abd progA (Seq ss) post)
                     where abd = CAbducible fName fParams
    Seq (s:ss)    -> rhleVCs $ RHLETrip (hlSP pre s) progA (Seq ss) post
    If bexp s1 s2 -> (rhleVCs $ RHLETrip (CAnd pre c) progA s1 post)
                  ++ (rhleVCs $ RHLETrip (CAnd pre (CNot c)) progA s2 post)
                     where c = bexpToCond bexp
    Call (UFunc fName fParams fPre fPost)
                  -- Assumes progA is SKIP, and so the VC (by the Skip RHLE rule) is:
                  --   (phi -> pre) & (a -> post) & a  =>  (a -> psi)
                  -- which is equivalent to:
                  --   (phi -> pre) & post & a  =>  psi
                  -> [abduce (CAnd (CImp pre fPreC) fPostC) post]
                     where fPreC = bexpToCond fPre
                           fPostC = bexpToCond fPost
stepR _ = error "stepR currently requires that progA be SKIP"
