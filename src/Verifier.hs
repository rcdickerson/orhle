module Verifier
    ( Abducible(..)
    , Abduction
    , setupAbduction
    , verify
    ) where

import Conditions
import Hoare
import HoareE
import Imp
import RHLE
import Z3.Monad

-- TODO
verify :: RHLETrip -> Bool
verify trip@(RHLETrip pre progA progE post) = True

setupAbduction :: RHLETrip -> Abduction
setupAbduction trip = step trip ([], [])

step :: RHLETrip -> Abduction -> Abduction
step trip@(RHLETrip pre progA progE post) abd@(ducs, conds) =
  case progA of
    Skip -> case progE of
              Skip -> abd
              _    -> stepE trip abd
    _    -> stepA trip abd

stepA :: RHLETrip -> Abduction -> Abduction
stepA (RHLETrip pre progA progE post) abd@(ducs, conds) =
  case progA of
    Skip -> abd
    Seq [] -> step (RHLETrip pre Skip progE post) abd
    Seq (s:ss) -> step (RHLETrip (hlSP pre s) (Seq ss) progE post) (ducs, (hlSP pre s) : conds)
    var := aexp -> (ducs, (hlSP pre (var := aexp)) : conds)
    If b s1 s2 -> (ducs1 ++ ducs2, conds1 ++ conds2)
                  where
                    (ducs1, conds1) = step (RHLETrip (CAnd pre c) s1 progE post) abd
                    (ducs2, conds2) = step (RHLETrip (CAnd pre (CNot c)) s2 progE post) abd
                    c = bexpToCond b
    call@(Call _) -> (ducs, (hlSP pre call) : conds)

stepE :: RHLETrip -> Abduction -> Abduction
stepE (RHLETrip pre progA progE post) abd@(ducs, conds) =
  case progE of
    Skip -> abd
    Seq [] -> step (RHLETrip pre progA Skip post) abd
    Seq ((Call f):ss) ->
      step (RHLETrip (erase pre $ fParams f) progA (Seq ss) post) ((Abducible f) : ducs, conds)
    Seq (s:ss) ->
      step (RHLETrip (hlSP pre s) progA (Seq ss) post) (ducs, (hlSP pre s) : conds)
    var := aexp -> (ducs, (hlSP pre (var := aexp)) : conds)
    If b s1 s2 -> (ducs1 ++ ducs2, conds1 ++ conds2)
                  where
                    (ducs1, conds1) = step (RHLETrip (CAnd pre c) progA s1 post) abd
                    (ducs2, conds2) = step (RHLETrip (CAnd pre (CNot c)) progA s2 post) abd
                    c = bexpToCond b
    Call f -> ((Abducible f) : ducs, conds)

erase :: Cond -> [Var] -> Cond
erase cond vars = cond -- TODO

data Abducible = Abducible
  { func :: UFunc } deriving (Show)

type Abduction = ([Abducible], [Cond])
