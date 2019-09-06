module Verifier2
  ( VResult
  , VTrace
  , ppVTrace
  , runVerifier2
  , verify2
  ) where

import Abduction
import Control.Monad.Trans
import Control.Monad.Writer
import Data.List(intercalate)
import qualified Data.Map as Map
import Hoare
import HoareE
import Imp
import InterpMap
import RHLE
import VTrace
import Z3.Monad
import Z3Util

type VResult       = Either String InterpMap
type VTracedResult = WriterT [VTrace] Z3 VResult

runVerifier2 :: String -> Prog -> Prog -> String -> IO String
runVerifier2 pre progA progE post = do
  (_, result) <- evalZ3 $ runWriterT $ runVerifier2' pre progA progE post
  return result

runVerifier2' :: String -> Prog -> Prog -> String -> WriterT String Z3 ()
runVerifier2' pre progA progE post = do
  tell "------------------------------------------------\n"
  tell $ "Universal Program:\n" ++ (show progA) ++ "\n"
  tell "------------------------------------------------\n"
  tell $ "Existential Program:\n" ++ (show progE) ++ "\n"
  tell "------------------------------------------------\n"
  trip <- lift $ mkRHLETrip pre progA progE post
  (result, trace) <- lift $ verify2 trip
  traceStr <- lift $ ppVTrace trace
  tell $ "Verification Trace:\n" ++ traceStr ++ "\n"
  tell "------------------------------------------------\n"
  case result of
    Right interp -> do
      tell "VALID iff the following executions are possible:\n"
      let funNames = assigneeToFuncNames (Seq [progA, progE])
      let funMap   = Map.mapKeys (\v -> Map.findWithDefault v v funNames) interp
      mapLines <- lift $ ppInterpMap funMap
      tell $ intercalate "\n" mapLines
      tell $ "\n"
    Left reason -> do
      tell $ "INVALID: " ++ reason ++ "\n"
  tell "------------------------------------------------"

assigneeToFuncNames :: Prog -> Map.Map Var String
assigneeToFuncNames prog =
  case prog of
    Seq s      -> Map.unions $ map assigneeToFuncNames s
    If _ s1 s2 -> Map.unions $ map assigneeToFuncNames [s1, s2]
    Call v (UFunc name _ _ _)
               -> Map.singleton v name
    _          -> Map.empty

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
    s@(_ := _) -> do
      pre'  <- lift $ hlSP s pre
      verifyE (HLETrip pre' progE post) imap
    If b s1 s2 -> do
      cond <- lift $ bexpToZ3 b
      verifyAIf cond s1 s2 [] (HLETrip pre progE post) imap
    Call var f -> return.Left $
        "Function calls in universal execution currently unsupported"

verifyASeq :: AST -> [Stmt] -> Prog -> AST -> InterpMap -> VTracedResult
verifyASeq pre [] progE post imap =
  verifyA (RHLETrip pre Skip progE post) imap
verifyASeq pre ((If b s1 s2):ss) progE post imap = do
  cond <- lift $ bexpToZ3 b
  verifyAIf cond s1 s2 ss (HLETrip pre progE post) imap
verifyASeq pre (s:ss) progE post imap = do
  pre'  <- lift $ hlSP s pre
  verifyA (RHLETrip pre' (Seq ss) progE post) imap

verifyAIf :: AST -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf c s1 s2 rest (HLETrip pre progE post) imap = do
  notC    <- lift $ mkNot c
  cond1   <- lift $ mkAnd [pre, c]
  cond2   <- lift $ mkAnd [pre, notC]
  consistent1 <- lift $ checkSat cond1
  consistent2 <- lift $ checkSat cond2
  case (consistent1, consistent2) of
    (True , True ) -> verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap
    (True , False) -> do
      condStr <- lift $ astToString notC
      logMsgA $ "(A) Skipping inconsistent else branch: " ++ condStr
      inBranchLog c $ verifyA (RHLETrip cond1 s1 progE post) imap
    (False, True ) -> do
      condStr <- lift $ astToString c
      logMsgA $ "(A) Skipping inconsistent then branch: " ++ condStr
      inBranchLog notC $ verifyA (RHLETrip cond2 s2 progE post) imap
    (False, False) -> return.Left $ "(A) Neither if-branch is consistent"

verifyAIf' :: AST -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap = do
  notC    <- lift $ mkNot c
  cond1   <- lift $ mkAnd [pre, c]
  cond2   <- lift $ mkAnd [pre, notC]
  res1    <- inBranchLog c $ verifyA (RHLETrip cond1 (Seq $ s1:rest) progE post) imap
  case res1 of
    Left  err   -> return.Left $ err
    Right imap1 -> do
      res2 <- inBranchLog notC $ verifyA (RHLETrip cond2 (Seq $ s2:rest) progE post) imap
      case res2 of
        Left  err   -> return.Left $ err
        Right imap2 -> lift $ imapCondUnion (c, imap1) (notC, imap2) >>= return.Right

verifyE :: HLETrip -> InterpMap -> VTracedResult
verifyE trip@(HLETrip pre progE post) imap = do
  logHle trip
  case progE of
    Skip       -> verifyFinalImpl pre imap post
    Seq ss     -> verifyESeq pre ss post imap
    s@(_ := _) -> do
      pre' <- lift $ hlSP s pre
      verifyE (HLETrip pre' Skip post) imap
    If b s1 s2 -> do
      cond <- lift $ bexpToZ3 b
      verifyEIf cond s1 s2 pre [] post imap
    Call var f -> verifyECall var f (HLETrip pre Skip post) imap

verifyESeq :: AST -> [Stmt] -> AST -> InterpMap -> VTracedResult
verifyESeq pre [] post imap =
  verifyE (HLETrip pre Skip post) imap
verifyESeq pre ((If b s1 s2):ss) post imap = do
  cond <- lift $ bexpToZ3 b
  verifyEIf cond s1 s2 pre ss post imap
verifyESeq pre ((Call var f):ss) post imap =
  verifyECall var f (HLETrip pre (Seq ss) post) imap
verifyESeq pre (s:ss) post imap = do
  pre' <- lift $ hlSP s pre
  verifyE (HLETrip pre' (Seq ss) post) imap

verifyFinalImpl :: AST -> InterpMap -> AST -> VTracedResult
verifyFinalImpl pre imap post = do
  preStr  <- lift $ astToString pre
  postStr <- lift $ astToString post
  result  <- lift $ imapStrengthen pre imap post
  case result of
    Right imap' -> do
      interpLines <- lift $ ppInterpMap imap'
      logAbductionSuccess interpLines preStr postStr
      return.Right $ imap'
    Left err -> do
      logAbductionFailure preStr postStr
      return.Left $ err

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> VTracedResult
verifyECall asg f (HLETrip pre progE post) imap = do
  preStr <- lift $ astToString pre
  logCallE preStr (fPreSMT f)
  fPre <- lift $ fPreCond f
  preCondImp <- lift $ mkImplies pre fPre
  preCondSat <- lift $ checkValid preCondImp
  case preCondSat of
    False -> return.Left $
             "(E) Precondition not satisfied for " ++ (fName f)
    True  -> do
      pre' <- lift $ funSP f pre
      verifyE (HLETrip pre' progE post) imap

verifyEIf :: AST -> Prog -> Prog
          -> AST -> [Stmt] -> AST
          -> InterpMap
          -> VTracedResult
verifyEIf c s1 s2 pre rest post imap = do
  notC   <- lift $ mkNot c
  cond1  <- lift $ mkAnd [pre, c]
  cond2  <- lift $ mkAnd [pre, notC]
  (canEnter1, imap1) <- lift $ tryStrengthening pre imap c
  (canEnter2, imap2) <- lift $ tryStrengthening pre imap notC
  case (canEnter1, canEnter2) of
    (False, False) -> return.Left $ "(E) Neither if-branch is enterable"
    (True , False) -> do
      condStr <- lift $ astToString notC
      logMsgE $ "Skipping unenterable if-branch: " ++ condStr
      inBranchLog c $ verifyE (HLETrip cond1 (Seq $ s1:rest) post) imap1
    (False, True ) -> do
      condStr <- lift $ astToString c
      logMsgE $ "Skipping unenterable if-branch: " ++ condStr
      inBranchLog notC $ verifyE (HLETrip cond2 (Seq $ s2:rest) post) imap2
    (True , True ) -> do
      mapLines1 <- lift $ ppInterpMap imap1
      mapLines2 <- lift $ ppInterpMap imap2
      preStr    <- lift $ astToString pre
      cStr      <- lift $ astToString c
      logAbductionSuccess mapLines1 preStr cStr
      res1 <- inBranchLog c $ verifyE (HLETrip cond1 (Seq $ s1:rest) post) imap1
      notCStr <- lift $ astToString notC
      logAbductionSuccess mapLines2 preStr notCStr
      res2 <- inBranchLog notC $ verifyE (HLETrip cond2 (Seq $ s2:rest) post) imap2
      case (res1, res2) of
        (Right imap1', Right imap2') -> lift $ return.Right
                                        =<< imapCondUnion (c, imap1') (notC, imap2')
        (Right imap1', Left _      ) -> return.Right $ imap1'
        (Left _      , Right imap2') -> return.Right $ imap2'
        (Left _      , Left _      ) -> return.Left  $
          "(E) Both if-branches are enterable, but neither verifies"

tryStrengthening :: AST -> InterpMap -> AST -> Z3 (Bool, InterpMap)
tryStrengthening pre imap branchAST = do
  res <- imapStrengthen pre imap branchAST
  case res of
    Left  _     -> return (False, emptyIMap)
    Right imap' -> return (True,  imap')

inBranchLog :: AST -> VTracedResult -> VTracedResult
inBranchLog cond branch = do
  condStr <- lift $ astToString cond
  logBranchStart condStr
  result <- branch
  logBranchEnd
  return result
