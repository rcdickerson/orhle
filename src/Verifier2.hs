module Verifier2
  ( verify2
  , VResult(..)
  ) where

import Abduction
import Conditions
import Hoare
import Imp
import RHLE
import Z3.Monad

data VResult = Valid InterpMap
             | Invalid String

verify2 :: RHLETrip -> Z3 VResult
verify2 trip = do
  verifyA trip =<< (imapInit $ rhleProgE trip)

verifyA :: RHLETrip -> InterpMap -> Z3 VResult
verifyA (RHLETrip pre progA progE post) imap = do
  case progA of
    Skip       -> verifyE pre progE post imap
    Seq []     -> verifyA (RHLETrip pre Skip progE post) imap
    Seq (s:ss) -> verifyA (RHLETrip (hlSP pre s) (Seq ss) progE post) imap
    s@(_ := _) -> verifyE (hlSP pre s) progE post imap
    If b s1 s2 -> do
                  let c = bexpToCond b
                  res1 <- verifyA (RHLETrip (CAnd pre c) s1 progE post) imap
                  case res1 of
                    Valid imap1 -> do
                                   res2 <- verifyA (RHLETrip (CAnd pre (CNot c)) s2 progE post) imap
                                   case res2 of
                                     Valid imap2 -> do
                                                    imap' <- imapUnion imap1 imap2
                                                    return $ Valid imap'
                                     Invalid _   -> return res2
                    Invalid _   -> return res1
    Call var f -> do
                  let precondImp = CImp pre (fPreCond f)
                  precondSat <- checkBool precondImp
                  case precondSat of
                    False -> return $ Invalid ("Precondition not satisfied for " ++ (fName f))
                    True  -> verifyE (CFuncPost var pre $ fPreCond f) progE post imap

verifyE :: Cond -> Prog -> Cond -> InterpMap -> Z3 VResult
verifyE pre progE post imap = do
  case progE of
    Skip       -> do
                  result <- imapStrengthen pre imap post
                  case result of
                    IRSat imap' -> return $ Valid imap'
                    IRUnsat     -> return $ Invalid
                      "Overall precondition does not imply overall postcondition"
    Seq []     -> verifyE pre Skip post imap
    Seq ((Call var f):ss)
               -> do
                  let preCondImp = CImp pre $ fPreCond f
                  preCondCheckBool <- checkBool preCondImp
                  case preCondCheckBool of
                    False -> return $ Invalid ("Precondition not satisfied for " ++ (fName f))
                    True  -> verifyE (CFuncPost var pre $ fPostCond f) (Seq ss) post imap
    Seq (s:ss) -> verifyE (hlSP pre s) (Seq ss) post imap
    s@(_ := _) -> verifyE (hlSP pre s) Skip post imap
    If b s1 s2 -> do
                  let c = bexpToCond b
                  res1 <- verifyE (CAnd pre c) s1 post imap
                  res2 <- verifyE (CAnd pre (CNot c)) s2 post imap
                  case res1 of
                    Valid imap1  -> case res2 of
                                     Valid imap2 -> do
                                                    imap' <- imapUnion imap1 imap2
                                                    return $ Valid imap'
                                     Invalid _   -> return res1
                    Invalid msg1 -> case res2 of
                                     Valid _      -> return res2
                                     Invalid msg2 -> return $ Invalid $
                                       "Neither existential if-branch verifies: "
                                       ++ (show [msg1, msg2])
    call@(Call var f)
               -> do
                  precondSat <- checkBool $ CImp pre (fPreCond f)
                  case precondSat of
                    False -> return $ Invalid ("Precondition not satisfied for " ++ (fName f))
                    True  -> verifyE (CFuncPost var pre $ fPostCond f) Skip post imap

checkBool :: Cond -> Z3 Bool
checkBool cond = do
  push
  assert =<< condToZ3 cond
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False
