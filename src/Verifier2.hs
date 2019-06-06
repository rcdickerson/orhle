module Verifier2
  ( verify2
  , VResult(..)
  ) where

import Abduction
import Conditions
import Hoare
import HoareE
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
    Skip       -> verifyE (HLETrip pre progE post) imap
    Seq []     -> verifyA (RHLETrip pre Skip progE post) imap
    Seq (s:ss) -> verifyA (RHLETrip (hlSP pre s) (Seq ss) progE post) imap
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) progE post) imap
    If b s1 s2 -> verifyAIf (bexpToCond b) s1 s2 (HLETrip pre progE post) imap
    Call var f -> verifyECall var f (HLETrip pre progE post) imap

verifyAIf :: Cond -> Prog -> Prog -> HLETrip -> InterpMap -> Z3 VResult
verifyAIf c s1 s2 (HLETrip pre progE post) imap = do
  res1 <- verifyA (RHLETrip (CAnd pre c) s1 progE post) imap
  case res1 of
    Invalid _   -> return res1
    Valid imap1 -> do
      res2 <- verifyA (RHLETrip (CAnd pre (CNot c)) s2 progE post) imap
      case res2 of
        Invalid _   -> return res2
        Valid imap2 -> imapUnion imap1 imap2 >>= return.Valid

verifyE :: HLETrip -> InterpMap -> Z3 VResult
verifyE (HLETrip pre progE post) imap = do
  case progE of
    Skip       -> verifyFinalImpl pre imap post
    Seq []     -> verifyE (HLETrip pre Skip post) imap
    Seq ((Call var f):ss)
               -> verifyECall var f (HLETrip pre (Seq ss) post) imap
    Seq (s:ss) -> verifyE (HLETrip (hlSP pre s) (Seq ss) post) imap
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) Skip post) imap
    If b s1 s2 -> verifyEIf (bexpToCond b) s1 s2 (HLETrip pre Skip post) imap
    Call var f -> verifyECall var f (HLETrip pre Skip post) imap

verifyFinalImpl :: Cond -> InterpMap -> Cond -> Z3 VResult
verifyFinalImpl pre imap post = do
  result <- imapStrengthen pre imap post
  case result of
    IRSat imap' -> return $ Valid imap'
    IRUnsat     -> return $ Invalid
      "Overall precondition does not imply overall postcondition"

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> Z3 VResult
verifyECall asg f (HLETrip pre progE post) imap = do
  precondSat <- checkBool $ CImp pre $ fPreCond f
  case precondSat of
    False -> return $ Invalid ("Precondition not satisfied for " ++ (fName f))
    True  -> verifyE (HLETrip pre' progE post) imap
             where pre' = (CFuncPost asg pre $ fPreCond f)

verifyEIf :: Cond -> Prog -> Prog -> HLETrip -> InterpMap -> Z3 VResult
verifyEIf c s1 s2 (HLETrip pre progE post) imap = do
  res1 <- verifyE (HLETrip (CAnd pre c) s1 post) imap
  res2 <- verifyE (HLETrip (CAnd pre (CNot c)) s2 post) imap
  case res1 of
    Valid imap1  -> case res2 of
                      Valid imap2 -> imapUnion imap1 imap2 >>= return.Valid
                      Invalid _   -> return res1
    Invalid msg1 -> case res2 of
                      Valid _      -> return res2
                      Invalid msg2 -> return $ Invalid $
                                      "Neither existential if-branch verifies: "
                                      ++ (show [msg1, msg2])

checkBool :: Cond -> Z3 Bool
checkBool cond = do
  push
  assert =<< condToZ3 cond
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False
