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
import Data.List
import Hoare
import HoareE
import Imp
import RHLE
import Z3.Monad

data VResult = Valid   InterpMap
             | Invalid String

data VTrace = VTRhle RHLETrip
            | VTHle  HLETrip
            | VTAbduction Bool [String] Cond Cond
            | VTACall Cond Cond
            | VTECall Cond Cond
            | VTStartBranch Cond
            | VTEndBranch
            | VTAMessage String
            | VTEMessage String

type VTracedResult = WriterT [VTrace] Z3 VResult

verify2 :: RHLETrip -> Z3 (VResult, [VTrace])
verify2 trip = do
  imap <- imapInit $ rhleProgE trip
  runWriterT $ verifyA trip imap

verifyA :: RHLETrip -> InterpMap -> VTracedResult
verifyA trip@(RHLETrip pre progA progE post) imap = do
  tell [VTRhle trip]
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
    (True, True)   -> verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap
    (True, False)  -> do
                      condStr <- lift $ ppCond (CNot c)
                      tell [VTAMessage $ "Skipping inconsistent else branch: " ++ condStr]
                      tell [VTStartBranch c]
                      res <- verifyA (RHLETrip (CAnd pre c) s1 progE post) imap
                      tell [VTEndBranch]
                      return res
    (False, True)  -> do
                      condStr <- lift $ ppCond c
                      tell [VTAMessage $ "Skipping inconsistent then branch: " ++ condStr]
                      tell [VTStartBranch (CNot c)]
                      res <- verifyA (RHLETrip (CAnd pre (CNot c)) s2 progE post) imap
                      tell [VTEndBranch]
                      return res
    (False, False) -> return $ Invalid "Neither if-branch is consistent"

verifyAIf' :: Cond -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> VTracedResult
verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap = do
  tell [VTStartBranch c]
  res1 <- verifyA (RHLETrip (CAnd pre c) (Seq $ s1:rest) progE post) imap
  tell [VTEndBranch]
  case res1 of
    Invalid reason -> return $ Invalid reason
    Valid   imap1  -> do
      tell [VTStartBranch (CNot c)]
      res2 <- verifyA (RHLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) progE post) imap
      tell [VTEndBranch]
      case res2 of
        Invalid reason -> return $ Invalid reason
        Valid   imap2  -> lift $ imapUnion imap1 imap2 >>= return.Valid

verifyE :: HLETrip -> InterpMap -> VTracedResult
verifyE trip@(HLETrip pre progE post) imap = do
  tell [VTHle trip]
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
                   tell [VTAbduction True interpLines pre post]
                   return $ Valid imap'
    IRUnsat     -> do
                   tell [VTAbduction False [] pre post]
                   return $ Invalid "No satisfying interpretation found"

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> VTracedResult
verifyECall asg f (HLETrip pre progE post) imap = do
  tell [VTECall pre $ fPreCond f]
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
  tell [VTStartBranch c]
  res1 <- verifyE (HLETrip (CAnd pre c)        (Seq $ s1:rest) post) imap
  tell [VTEndBranch, VTStartBranch (CNot c)]
  res2 <- verifyE (HLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) post) imap
  tell [VTEndBranch]
  case res1 of
    Valid   imap1 -> case res2 of
                       Valid   imap2  -> lift $ imapUnion imap1 imap2 >>= return.Valid
                       Invalid reason -> return $ Valid imap1
    Invalid msg1  -> case res2 of
                       Valid   imap2 -> return $ Valid imap2
                       Invalid msg2  -> return $ Invalid
                                        $ "Neither existential if-branch verifies"

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

ppVTrace :: [VTrace] -> Z3 String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VTrace] -> Z3 String
ppVTrace' _ [] = return ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre progA progE post) -> do
      preStr <- ppCond pre
      progStr <- ppStmtStart progA
      rest   <- ppVTrace' indent ts
      return $ start ++ "A " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTHle  (HLETrip  pre progE post) -> do
      preStr  <- ppCond pre
      progStr <- ppStmtStart progE
      rest    <- ppVTrace' indent ts
      return $ start ++ "E " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTAbduction sat interpLines pre post -> do
      preStr  <- ppCond pre
      postStr <- ppCond post
      rest    <- ppVTrace' indent ts
      return $ start ++ (if sat then "O " else "X ")
        ++ "<Abduction> " ++ preStr ++ " -> " ++ postStr
        ++ (concat $ map (\line -> "\n" ++ start ++ "  :" ++ line) interpLines)
        ++ "\n" ++ rest
    VTACall pre fpre -> do
      preStr  <- ppCond pre
      fPreStr <- ppCond fpre
      rest    <- ppVTrace' indent ts
      return $ start ++ "A :: Precondition Check: "
        ++ preStr ++ " -> " ++ fPreStr
        ++ "\n" ++ rest
    VTECall pre fpre -> do
      preStr  <- ppCond pre
      fPreStr <- ppCond fpre
      rest    <- ppVTrace' indent ts
      return $ start ++ "E :: Precondition Check: "
        ++ preStr ++ " -> " ++ fPreStr
        ++ "\n" ++ rest
    VTStartBranch cond -> do
      condStr <- ppCond cond
      rest <- ppVTrace' (indent + 1) ts
      return $ start ++ "+ Branch: " ++ condStr ++ "\n" ++ rest
    VTEndBranch ->
      ppVTrace' (indent - 1) ts
    VTAMessage msg -> do
      rest <- ppVTrace' indent ts
      return $ start ++ "A :: " ++ msg ++ "\n" ++ rest
    VTEMessage msg -> do
      rest <- ppVTrace' indent ts
      return $ start ++ "E :: " ++ msg ++ "\n" ++ rest
  where
    start = (concat $ replicate indent "| ")

ppStmtStart :: Stmt -> Z3 String
ppStmtStart stmt =
  case stmt of
    Skip -> return "Skip"
    v := aexp -> do
      aexpStr <- astToString =<< aexpToZ3 aexp
      return $ v ++ " := " ++ aexpStr
    Seq [] -> return "Seq []"
    Seq (s:[]) -> ppStmtStart s
    Seq (s:ss) -> do
      first <- ppStmtStart s
      return $ first ++ "..."
    If b s1 s2 -> do
      condStr <- ppCond $ bexpToCond b
      thenStr <- ppStmtStart s1
      elseStr <- ppStmtStart s2
      return $ "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
    Call v (UFunc name params pre post) -> do
      return $ v ++ " := " ++ name ++ "(" ++ (intercalate ", " params) ++ ")"

ppCond :: Cond -> Z3 String
ppCond cond = astToString =<< simplify =<< condToZ3 cond
