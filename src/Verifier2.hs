module Verifier2
  ( ppVTrace
  , runVerifier2
  , verify2
  , VResult
  , VTrace
  ) where

import Abduction
import Control.Monad.Trans
import Control.Monad.Writer
import Data.List(intercalate)
import qualified Data.Map as Map
import Hoare
import HoareE
import Imp
import RHLE
import VTrace
import Z3.Monad
import Z3Util

type VResult       = Either String InterpMap
type VTracedResult = WriterT [VTrace] Z3 VResult

runVerifier2 :: RHLETrip -> IO String
runVerifier2 rhleTrip = do
  (_, result) <- evalZ3 $ runWriterT $ runVerifier2' rhleTrip
  return result

runVerifier2' :: RHLETrip -> WriterT String Z3 ()
runVerifier2' rhleTrip = do
  let progA = rhleProgA rhleTrip
  let progE = rhleProgE rhleTrip
  tell "------------------------------------------------\n"
  tell $ "Universal Program:\n" ++ (show progA) ++ "\n"
  tell "------------------------------------------------\n"
  tell $ "Existential Program:\n" ++ (show progE) ++ "\n"
  tell "------------------------------------------------\n"
  (result, trace) <- lift $ verify2 rhleTrip
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
      cond <- lift $ smtString =<< bexpToZ3 b
      verifyAIf cond s1 s2 [] (HLETrip pre progE post) imap
    Call var f -> return.Left $
        "Function calls in universal execution currently unsupported"

verifyASeq :: String -> [Stmt] -> Prog -> String -> InterpMap -> VTracedResult
verifyASeq pre [] progE post imap =
  verifyA (RHLETrip pre Skip progE post) imap
verifyASeq pre ((If b s1 s2):ss) progE post imap = do
  cond <- lift $ smtString =<< bexpToZ3 b
  verifyAIf cond s1 s2 ss (HLETrip pre progE post) imap
verifyASeq pre (s:ss) progE post imap = do
  pre'  <- lift $ hlSP s pre
  verifyA (RHLETrip pre' (Seq ss) progE post) imap

verifyAIf :: SMTString -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf c s1 s2 rest trip@(HLETrip pre progE post) imap = do
  cAST    <- lift $ parseSMT c
  notC    <- lift $ mkNot cAST
  preAST  <- lift $ hlePreAST trip
  postAST <- lift $ hlePostAST trip
  cond1   <- lift $ mkAnd [preAST, cAST]
  cond2   <- lift $ mkAnd [preAST, notC]
  consistent1 <- lift $ checkSat cond1
  consistent2 <- lift $ checkSat cond2
  case (consistent1, consistent2) of
    (True , True ) -> verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap
    (True , False) -> do
      condStr <- lift $ smtString notC
      logMsgA $ "(A) Skipping inconsistent else branch: " ++ condStr
      trip'   <- lift $ mkRHLETripFromASTs cond1 s1 progE postAST
      inBranchLog c $ verifyA trip' imap
    (False, True ) -> do
      logMsgA $ "(A) Skipping inconsistent then branch: " ++ c
      trip'   <- lift $ mkRHLETripFromASTs cond2 s2 progE postAST
      notCStr <- lift $ smtString notC
      inBranchLog notCStr $ verifyA trip' imap
    (False, False) -> return.Left $ "(A) Neither if-branch is consistent"

verifyAIf' :: SMTString -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf' c s1 s2 rest trip@(HLETrip pre progE post) imap = do
  cAST    <- lift $ parseSMT c
  notC    <- lift $ mkNot cAST
  preAST  <- lift $ hlePreAST trip
  postAST <- lift $ hlePostAST trip
  cond1   <- lift $ mkAnd [preAST, cAST]
  cond2   <- lift $ mkAnd [preAST, notC]
  trip'   <- lift $ mkRHLETripFromASTs cond1 (Seq $ s1:rest) progE postAST
  res1    <- inBranchLog c $ verifyA trip' imap
  case res1 of
    Left  err   -> return.Left $ err
    Right imap1 -> do
      trip'' <- lift $ mkRHLETripFromASTs cond2 (Seq $ s2:rest) progE postAST
      res2   <- inZ3BranchLog notC $ verifyA trip'' imap
      case res2 of
        Left  err   -> return.Left $ err
        Right imap2 -> do
          notCStr <- lift $ smtString notC
          lift $ imapCondUnion (c, imap1) (notCStr, imap2) >>= return.Right

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
      cond <- lift $ smtString =<< bexpToZ3 b
      verifyEIf cond s1 s2 pre [] post imap
    Call var f -> verifyECall var f (HLETrip pre Skip post) imap

verifyESeq :: SMTString -> [Stmt] -> SMTString -> InterpMap -> VTracedResult
verifyESeq pre [] post imap =
  verifyE (HLETrip pre Skip post) imap
verifyESeq pre ((If b s1 s2):ss) post imap = do
  cond <- lift $ smtString =<< bexpToZ3 b
  verifyEIf cond s1 s2 pre ss post imap
verifyESeq pre ((Call var f):ss) post imap =
  verifyECall var f (HLETrip pre (Seq ss) post) imap
verifyESeq pre (s:ss) post imap = do
  pre' <- lift $ hlSP s pre
  verifyE (HLETrip pre' (Seq ss) post) imap

verifyFinalImpl :: String -> InterpMap -> String -> VTracedResult
verifyFinalImpl pre imap post = do
  result <- lift $ imapStrengthen pre imap post
  case result of
    Right imap' -> do
      interpLines <- lift $ ppInterpMap imap'
      logAbductionSuccess interpLines pre post
      return.Right $ imap'
    Left err -> do
      logAbductionFailure pre post
      return.Left $ err

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> VTracedResult
verifyECall asg f (HLETrip pre progE post) imap = do
  logCallE pre $ fPreCond f
  preAST  <- lift $ parseSMT pre
  fPreAST <- lift $ fPreCondAST f
  preCondImp <- lift $ mkImplies preAST fPreAST
  preCondSat <- lift $ checkValid preCondImp
  case preCondSat of
    False -> return.Left $
             "(E) Precondition not satisfied for " ++ (fName f)
    True  -> do
      pre' <- lift $ funSP f pre
      verifyE (HLETrip pre' progE post) imap

verifyEIf :: SMTString -> Prog -> Prog
          -> SMTString -> [Stmt] -> SMTString
          -> InterpMap
          -> VTracedResult
verifyEIf c s1 s2 pre rest post imap = do
  preAST <- lift $ parseSMT pre
  cAST   <- lift $ parseSMT c
  notC   <- lift $ mkNot cAST
  cond1  <- lift $ smtString =<< mkAnd [preAST, cAST]
  cond2  <- lift $ smtString =<< mkAnd [preAST, notC]
  (canEnter1, imap1) <- lift $ tryStrengthening pre imap c
  (canEnter2, imap2) <- lift $ tryStrengthening pre imap =<< smtString notC
  case (canEnter1, canEnter2) of
    (False, False) -> return.Left $ "(E) Neither if-branch is enterable"
    (True , False) -> do
      condStr <- lift $ astToString notC
      logMsgE $ "Skipping unenterable if-branch: " ++ condStr
      inBranchLog c $ verifyE (HLETrip cond1 (Seq $ s1:rest) post) imap1
    (False, True ) -> do
      logMsgE $ "Skipping unenterable if-branch: " ++ c
      inZ3BranchLog notC $ verifyE (HLETrip cond2 (Seq $ s2:rest) post) imap2
    (True , True ) -> do
      mapLines1 <- lift $ ppInterpMap imap1
      mapLines2 <- lift $ ppInterpMap imap2
      logAbductionSuccess mapLines1 pre c
      res1 <- inBranchLog c $ verifyE (HLETrip cond1 (Seq $ s1:rest) post) imap1
      notCStr <- lift $ smtString notC
      logAbductionSuccess mapLines2 pre notCStr
      res2 <- inZ3BranchLog notC $ verifyE (HLETrip cond2 (Seq $ s2:rest) post) imap2
      case (res1, res2) of
        (Right imap1', Right imap2') -> lift $ return.Right
                                        =<< imapCondUnion (c, imap1') (notCStr, imap2')
        (Right imap1', Left _      ) -> return.Right $ imap1'
        (Left _      , Right imap2') -> return.Right $ imap2'
        (Left _      , Left _      ) -> return.Left  $
          "(E) Both if-branches are enterable, but neither verifies"

tryStrengthening :: SMTString -> InterpMap -> SMTString -> Z3 (Bool, InterpMap)
tryStrengthening pre imap branchAST = do
  res <- imapStrengthen pre imap branchAST
  case res of
    Left  _     -> return (False, emptyIMap)
    Right imap' -> return (True,  imap')

inZ3BranchLog :: AST -> VTracedResult -> VTracedResult
inZ3BranchLog cond branch = do
  condStr <- lift $ smtString cond
  inBranchLog condStr branch

inBranchLog :: SMTString -> VTracedResult -> VTracedResult
inBranchLog cond branch = do
  logBranchStart cond
  result <- branch
  logBranchEnd
  return result
