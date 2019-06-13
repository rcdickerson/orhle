module Verifier2
  ( ppVTrace
  , verify2
  , VResult(..)
  , VTrace
  ) where

import Abduction
import Conditions
import Control.Monad.Trans
import Control.Monad.Writer
import Hoare
import HoareE
import Imp
import RHLE
import VTrace
import Z3.Monad

data VResult = Valid   InterpMap
             | Invalid String

type VTracedResult = WriterT [VTrace] Z3 VResult

verify2 :: RHLETrip -> Z3 (VResult, [VTrace])
verify2 trip = do
  imap <- imapInit $ rhleProgE trip
  runWriterT $ verifyA trip imap

verifyA :: RHLETrip -> InterpMap -> VTracedResult
verifyA trip@(RHLETrip pre progA progE post) imap = do
  logRhle trip
  case progA of
    Skip       -> verifyE (HLETrip pre progE post) imap
    Seq ss     -> verifyASeq pre ss progE post imap
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) progE post) imap
    If b s1 s2 -> verifyAIf (bexpToCond b) s1 s2 [] (HLETrip pre progE post) imap
    Call var f -> return $ Invalid
        "Function calls in universal execution currently unsupported"

verifyASeq :: Cond -> [Stmt] -> Prog -> Cond -> InterpMap -> VTracedResult
verifyASeq pre [] progE post imap =
  verifyA (RHLETrip pre Skip progE post) imap
verifyASeq pre ((If b s1 s2):ss) progE post imap =
  verifyAIf (bexpToCond b) s1 s2 ss (HLETrip pre progE post) imap
verifyASeq pre (s:ss) progE post imap =
  verifyA (RHLETrip (hlSP pre s) (Seq ss) progE post) imap

verifyAIf :: Cond -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf c s1 s2 rest (HLETrip pre progE post) imap = do
  consistent1 <- lift $ checkSat (CAnd pre c)
  consistent2 <- lift $ checkSat (CAnd pre (CNot c))
  case (consistent1, consistent2) of
    (True , True ) -> verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap
    (True , False) -> do
      condStr <- lift $ condZ3String (CNot c)
      logMsgA $ "Skipping inconsistent else branch: " ++ condStr
      inBranchLog c $ verifyA (RHLETrip (CAnd pre c) s1 progE post) imap
    (False, True ) -> do
      condStr <- lift $ condZ3String c
      logMsgA $ "Skipping inconsistent then branch: " ++ condStr
      inBranchLog (CNot c) $ verifyA (RHLETrip (CAnd pre (CNot c)) s2 progE post) imap
    (False, False) -> return $ Invalid "Neither if-branch is consistent"

verifyAIf' :: Cond -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap = do
  res1 <- inBranchLog c $ verifyA (RHLETrip (CAnd pre c) (Seq $ s1:rest) progE post) imap
  case res1 of
    Invalid reason -> return $ Invalid reason
    Valid   imap1  -> do
      res2 <- inBranchLog (CNot c)
          $ verifyA (RHLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) progE post) imap
      case res2 of
        Invalid reason -> return $ Invalid reason
        Valid   imap2  -> lift $ imapUnion imap1 imap2 >>= return.Valid

verifyE :: HLETrip -> InterpMap -> VTracedResult
verifyE trip@(HLETrip pre progE post) imap = do
  logHle trip
  case progE of
    Skip       -> verifyFinalImpl pre imap post
    Seq ss     -> verifyESeq pre ss post imap
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) Skip post) imap
    If b s1 s2 -> verifyEIf (bexpToCond b) s1 s2 pre [] post imap
    Call var f -> verifyECall var f (HLETrip pre Skip post) imap

verifyESeq :: Cond -> [Stmt] -> Cond -> InterpMap -> VTracedResult
verifyESeq pre [] post imap =
  verifyE (HLETrip pre Skip post) imap
verifyESeq pre ((If b s1 s2):ss) post imap =
  verifyEIf (bexpToCond b) s1 s2 pre ss post imap
verifyESeq pre ((Call var f):ss) post imap =
  verifyECall var f (HLETrip pre (Seq ss) post) imap
verifyESeq pre (s:ss) post imap =
  verifyE (HLETrip (hlSP pre s) (Seq ss) post) imap

verifyFinalImpl :: Cond -> InterpMap -> Cond -> VTracedResult
verifyFinalImpl pre imap post = do
  result <- lift $ imapStrengthen pre imap post
  case result of
    IRSat imap' -> do
      interpLines <- lift $ ppInterpMap imap'
      logAbductionSuccess interpLines pre post
      return $ Valid imap'
    IRUnsat -> do
      logAbductionFailure pre post
      return $ Invalid "No satisfying interpretation found"

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> VTracedResult
verifyECall asg f (HLETrip pre progE post) imap = do
  logCallE pre $ fPreCond f
  precondSat <- lift $ checkValid $ CImp pre $ fPreCond f
  case precondSat of
    False -> return $ Invalid $
             "Precondition not satisfied for " ++ (fName f)
    True  -> verifyE (HLETrip pre' progE post) imap
             where pre'  = CFuncPost asg f pre

verifyEIf :: Cond -> Prog -> Prog
          -> Cond -> [Stmt] -> Cond
          -> InterpMap
          -> VTracedResult
verifyEIf c s1 s2 pre rest post imap = do
  (canEnter1, imap1) <- lift $ tryStrengthening pre imap c
  (canEnter2, imap2) <- lift $ tryStrengthening pre imap (CNot c)
  case (canEnter1, canEnter2) of
    (False, False) -> return $ Invalid "Neither existential if-branch is enterable"
    (True , False) -> do
      condStr <- lift $ condZ3String (CNot c)
      logMsgE $ "Skipping unenterable if-branch: " ++ condStr
      inBranchLog c $ verifyE (HLETrip (CAnd pre c) (Seq $ s1:rest) post) imap1
    (False, True ) -> do
      condStr <- lift $ condZ3String c
      logMsgE $ "Skipping unenterable if-branch: " ++ condStr
      inBranchLog (CNot c) $ verifyE (HLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) post) imap2
    (True , True ) -> do
      mapLines1 <- lift $ ppInterpMap imap1
      mapLines2 <- lift $ ppInterpMap imap2
      logAbductionSuccess mapLines1 pre c
      res1 <- inBranchLog c $ verifyE (HLETrip (CAnd pre c) (Seq $ s1:rest) post) imap1
      logAbductionSuccess mapLines2 pre (CNot c)
      res2 <- inBranchLog c $ verifyE (HLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) post) imap2
      case (res1, res2) of
        (Valid imap1', Valid imap2') -> lift $ imapUnion imap1' imap2' >>= return.Valid
        (Valid imap1', Invalid _   ) -> return $ Valid imap1'
        (Invalid _   , Valid imap2') -> return $ Valid imap2'
        (Invalid _   , Invalid _   ) -> return $ Invalid
          "Both existential if-branches are enterable, but neither verifies"

tryStrengthening :: Cond -> InterpMap -> Cond -> Z3 (Bool, InterpMap)
tryStrengthening pre imap branchCond = do
  res <- imapStrengthen pre imap branchCond
  case res of
    IRSat imap' -> return (True, imap')
    IRUnsat     -> return (False, emptyIMap)

inBranchLog :: Cond -> VTracedResult -> VTracedResult
inBranchLog cond branch = do
  logBranchStart cond
  result <- branch
  logBranchEnd
  return result

checkValid :: Cond -> Z3 Bool
checkValid cond = do
  push
  assert =<< mkNot =<< condToZ3 cond
  result <- check
  pop 1
  case result of
    Unsat -> return True
    _     -> return False

checkSat :: Cond -> Z3 Bool
checkSat cond = do
  push
  assert =<< condToZ3 cond
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False
