module Verifier2
  ( ppVTrace
  , verify2
  , VResult(..)
  , VTrace
  ) where

import Abduction
import Conditions
import Hoare
import HoareE
import Imp
import RHLE
import Z3.Monad

data VResult = Valid   [VTrace] InterpMap
             | Invalid [VTrace] String

data VTrace = VTRhle RHLETrip
            | VTHle  HLETrip
            | VTAbduction Bool InterpMap Cond Cond
            | VTCall Cond Cond
            | VTBranch [VTrace] [VTrace]

verify2 :: RHLETrip -> Z3 VResult
verify2 trip = do
  imap <- imapInit $ rhleProgE trip
  verifyA trip imap []

verifyA :: RHLETrip -> InterpMap -> [VTrace] -> Z3 VResult
verifyA trip@(RHLETrip pre progA progE post) imap trace = do
  case progA of
    Skip       -> verifyE (HLETrip pre progE post) imap trace'
    Seq ss     -> verifyASeq pre ss progE post imap trace'
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) progE post) imap trace'
    If b s1 s2 -> verifyAIf (bexpToCond b) s1 s2 [] (HLETrip pre progE post) imap trace'
    Call var f -> return $ Invalid trace'
        "Function calls in universal execution currently unsupported"
  where trace' = trace ++ [VTRhle trip]

verifyASeq :: Cond -> [Stmt] -> Prog -> Cond -> InterpMap -> [VTrace] -> Z3 VResult
verifyASeq pre [] progE post imap trace =
  verifyA (RHLETrip pre Skip progE post) imap trace
verifyASeq pre ((If b s1 s2):ss) progE post imap trace =
  verifyAIf (bexpToCond b) s1 s2 ss (HLETrip pre progE post) imap trace
verifyASeq pre (s:ss) progE post imap trace =
  verifyA (RHLETrip (hlSP pre s) (Seq ss) progE post) imap trace

verifyAIf :: Cond -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> [VTrace] -> Z3 VResult
verifyAIf c s1 s2 rest (HLETrip pre progE post) imap trace = do
  consistent1 <- checkSat (CAnd pre c)
  consistent2 <- checkSat (CAnd pre (CNot c))
  if consistent1 then
    if consistent2 then
      verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap trace
    else
      verifyA (RHLETrip (CAnd pre c) s1 progE post) imap trace
  else
    if consistent2 then
      verifyA (RHLETrip (CAnd pre (CNot c)) s2 progE post) imap trace
    else
      return $ Invalid trace "Neither if-branch is consistent"

verifyAIf' :: Cond -> Prog -> Prog -> [Stmt] -> HLETrip -> InterpMap -> [VTrace] -> Z3 VResult
verifyAIf' c s1 s2 rest (HLETrip pre progE post) imap trace = do
  res1 <- verifyA (RHLETrip (CAnd pre c) (Seq $ s1:rest) progE post) imap []
  case res1 of
    Invalid tr1 reason -> return $ Invalid (trace ++ tr1) reason
    Valid   tr1 imap1  -> do
      res2 <- verifyA (RHLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) progE post) imap []
      case res2 of
        Invalid tr2 reason -> return $ Invalid
          (trace ++ [VTBranch tr1 tr2]) reason
        Valid tr2 imap2    -> imapUnion imap1 imap2 >>= return.Valid
          (trace ++ [VTBranch tr1 tr2])

verifyE :: HLETrip -> InterpMap -> [VTrace] -> Z3 VResult
verifyE trip@(HLETrip pre progE post) imap trace = do
  case progE of
    Skip       -> verifyFinalImpl pre imap post trace'
    Seq ss     -> verifyESeq pre ss post imap trace'
    s@(_ := _) -> verifyE (HLETrip (hlSP pre s) Skip post) imap trace'
    If b s1 s2 -> verifyEIf (bexpToCond b) s1 s2 pre [] post imap trace'
    Call var f -> verifyECall var f (HLETrip pre Skip post) imap trace'
  where trace' = trace ++ [VTHle trip]

verifyESeq :: Cond -> [Stmt] -> Cond -> InterpMap -> [VTrace] -> Z3 VResult
verifyESeq pre [] post imap trace =
  verifyE (HLETrip pre Skip post) imap trace
verifyESeq pre ((If b s1 s2):ss) post imap trace =
  verifyEIf (bexpToCond b) s1 s2 pre ss post imap trace
verifyESeq pre ((Call var f):ss) post imap trace =
  verifyECall var f (HLETrip pre (Seq ss) post) imap trace
verifyESeq pre (s:ss) post imap trace =
  verifyE (HLETrip (hlSP pre s) (Seq ss) post) imap trace

verifyFinalImpl :: Cond -> InterpMap -> Cond -> [VTrace] -> Z3 VResult
verifyFinalImpl pre imap post trace = do
  result <- imapStrengthen pre imap post
  case result of
    IRSat imap' -> return $ Valid (trace ++ [VTAbduction True imap pre post]) imap'
    IRUnsat     -> return $ Invalid (trace ++ [VTAbduction False imap pre post])
        "No interpretation satisfying overall pre and post condition."

verifyECall :: Var -> UFunc -> HLETrip -> InterpMap -> [VTrace] -> Z3 VResult
verifyECall asg f (HLETrip pre progE post) imap trace = do
  let trace' = trace ++ [VTCall pre $ fPreCond f]
  precondSat <- checkValid $ CImp pre $ fPreCond f
  case precondSat of
    False -> return $ Invalid trace' $
        "Precondition not satisfied for " ++ (fName f)
    True  -> verifyE (HLETrip pre' progE post) imap trace'
             where pre'  = CFuncPost asg f pre

verifyEIf :: Cond -> Prog -> Prog
          -> Cond -> [Stmt] -> Cond
          -> InterpMap -> [VTrace] -> Z3 VResult
verifyEIf c s1 s2 pre rest post imap trace = do
  res1 <- verifyE (HLETrip (CAnd pre c)        (Seq $ s1:rest) post) imap []
  res2 <- verifyE (HLETrip (CAnd pre (CNot c)) (Seq $ s2:rest) post) imap []
  case res1 of
    Valid tr1 imap1  -> case res2 of
                      Valid tr2 imap2    -> imapUnion imap1 imap2 >>= return.Valid
                                            (trace ++ [VTBranch tr1 tr2])
                      Invalid tr2 reason -> return $ Valid
                                            (trace ++ [VTBranch tr1 tr2]) imap1
    Invalid tr1 msg1 -> case res2 of
                      Valid tr2 imap2  -> return $ Valid
                                          (trace ++ [VTBranch tr1 tr2]) imap2
                      Invalid tr2 msg2 -> return $ Invalid
                                          (trace ++ [VTBranch tr1 tr2])
                                          $ "Neither existential if-branch verifies: "
                                             ++ (show [msg1, msg2])

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

ppVTrace :: [VTrace] -> String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VTrace] -> String
ppVTrace' _ [] = ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre progA progE post) -> start ++ "A "
                                              ++ (ppCond pre) ++ " :: "
                                              ++ (show progA) ++ rest
    VTHle  (HLETrip  pre progE post) -> start ++ "E "
                                        ++ (ppCond pre)
                                        ++ " :: "
                                        ++ (show progE) ++ rest
    VTAbduction sat imap pre post -> start
                                     ++ (if sat then "O " else "X ")
                                     ++ "<Abduction> "
                                     ++ (ppCond pre) ++ " -> " ++ (ppCond post)
                                     ++ rest
    VTCall pre fpre -> start ++ "<Call> "
                       ++ (ppCond pre) ++ " -> " ++ (ppCond fpre)
                       ++ rest
    VTBranch left right -> start ++ "+\n"
                           ++ (ppVTrace' (indent + 1) left)
                           ++ start ++ "+\n"
                           ++ (ppVTrace' (indent + 1) right)
                           ++ (ppVTrace' indent ts)
  where
    start = (concat $ replicate indent "| ")
    rest  = "\n" ++ (ppVTrace' indent ts)

ppCond :: Cond -> String
ppCond cond =
  case cond of
    CTrue -> "true"
    CFalse -> "false"
    CEq lhs rhs -> (ppAExp lhs) ++ " = " ++ (ppAExp rhs)
    CNot c -> "~" ++ "(" ++ (ppCond c) ++ ")"
    CAnd c1 c2 -> (ppCond c1) ++ " /\\ " ++ (ppCond c2)
    COr c1 c2 -> (ppCond c1) ++ " \\/ " ++ (ppCond c2)
    CImp c1 c2 -> "(" ++ (ppCond c1) ++ ") -> (" ++ (ppCond c2) ++ ")"
    CAssignPost var aexp p -> (ppCond p) ++ " /\\ " ++ var ++ " = " ++ (ppAExp aexp)
    CFuncPost var f pre -> ppCond $ CAnd pre (fPostCond f)

ppAExp :: AExp -> String
ppAExp aexp =
  case aexp of
    I i -> show i
    V v -> v
    lhs :+: rhs -> (ppAExp lhs) ++ " + " ++ (ppAExp rhs)
    lhs :-: rhs -> (ppAExp lhs) ++ " - " ++ (ppAExp rhs)
    lhs :*: rhs -> (ppAExp lhs) ++ " * " ++ (ppAExp rhs)
    AMod lhs rhs -> (ppAExp lhs) ++ " % " ++ (ppAExp rhs)
