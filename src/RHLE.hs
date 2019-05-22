module RHLE
  ( rhleEncode
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

-- The given triple is valid iff the conjunction of the returned
-- conditions is unsatisfiable.
rhleEncode :: RHLETrip -> [Cond]
rhleEncode trip@(RHLETrip pre _ _ post) =
  pre : (CNot post) : (stepThrough trip)

stepThrough :: RHLETrip -> [Cond]
stepThrough trip =
  case (rhleProgA trip) of
    Skip -> stepR trip
    _    -> stepL trip

stepL :: RHLETrip -> [Cond]
stepL (RHLETrip pre progA progE post) =
  case progA of
    Skip          -> [hlSP pre Skip]
    Seq []        -> stepThrough $ RHLETrip pre Skip progE post
    Seq (s:ss)    -> (hlSP pre s)
                   : (stepThrough $ RHLETrip (hlSP pre s) (Seq ss) progE post)
    var := aexp   -> [hlSP pre (var := aexp)]
    If b s1 s2    -> (stepThrough $ RHLETrip (CAnd pre c) s1 progE post)
                  ++ (stepThrough $ RHLETrip (CAnd pre (CNot c)) s2 progE post)
                     where c = bexpToCond b
    call@(Call _) -> [hlSP pre call]

stepR :: RHLETrip -> [Cond]
stepR (RHLETrip pre progA progE post) =
  case progE of
    Skip          -> [hleSP pre Skip]
    Seq[]         -> stepThrough $ RHLETrip pre progA Skip post
    Seq (s:ss)    -> (hleSP pre s)
                   : (stepThrough $ RHLETrip (hleSP pre s) progA (Seq ss) post)
    var := aexp   -> [hleSP pre (var := aexp)]
    If b s1 s2    -> (stepThrough $ RHLETrip (CAnd pre c) progA s1 post)
                  ++ (stepThrough $ RHLETrip (CAnd pre (CNot c)) progA s2 post)
                     where c = bexpToCond b
    call@(Call _) -> [hleSP pre call]
