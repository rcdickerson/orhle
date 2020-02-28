module VerifierTrace
  ( VerifierTrace
  , VTWriter
  , logAbductionFailure
  , logAbductionSuccess
  , logBranchEnd
  , logBranchStart
  , logCallA
  , logCallE
  , logHle
  , logMsg
  , logMsgA
  , logMsgE
  , logRhle
  , ppVTrace
  ) where

import Control.Monad.Writer
import Data.List
import Imp
import Triples
import Z3.Monad

data VerifierTrace = VTRhle RHLETrip
                   | VTHle  HLETrip
                   | VTAbduction Bool [String] String String
                   | VTCall VTKind String String
                   | VTStartBranch String
                   | VTEndBranch
                   | VTMessage VTKind String

data VTKind = VTKindA | VTKindE | VTKindGeneral

type VTWriter m a = WriterT [VerifierTrace] m a

logRhle :: (Monad m) => RHLETrip -> VTWriter m ()
logRhle trip = do tell [VTRhle trip]

logHle :: (Monad m) => HLETrip -> VTWriter m ()
logHle trip = do tell [VTHle trip]

logMsg :: (Monad m) => String -> VTWriter m ()
logMsg msg = do tell [VTMessage VTKindGeneral msg]

logMsgA :: (Monad m) => String -> VTWriter m ()
logMsgA msg = do tell [VTMessage VTKindA msg]

logMsgE :: (Monad m) => String -> VTWriter m ()
logMsgE msg = do tell [VTMessage VTKindE msg]

logBranchStart :: (Monad m) => String -> VTWriter m ()
logBranchStart cond = do tell [VTStartBranch cond]

logBranchEnd :: (Monad m) => VTWriter m ()
logBranchEnd = do tell [VTEndBranch]

logAbductionSuccess :: (Monad m) => [String] -> String -> String -> VTWriter m ()
logAbductionSuccess interpLines pre post = do
  tell [VTAbduction True interpLines pre post]

logAbductionFailure :: (Monad m) => String -> String -> VTWriter m ()
logAbductionFailure pre post = do
  tell [VTAbduction False [] pre post]

logCallA :: (Monad m) => String -> String -> VTWriter m ()
logCallA pre post = do tell [VTCall VTKindA pre post]

logCallE :: (Monad m) => String -> String -> VTWriter m ()
logCallE pre post = do tell [VTCall VTKindE pre post]

ppVTrace :: [VerifierTrace] -> Z3 String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VerifierTrace] -> Z3 String
ppVTrace' _ [] = return ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre aProgs eProgs post) -> do
      progStr <- ppStmtsStart aProgs
      rest    <- ppVTrace' indent ts
      preStr  <- astToString pre
      return $ start ++ "A " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTHle  (HLETrip  pre progE post) -> do
      progStr <- ppStmtStart progE
      rest    <- ppVTrace' indent ts
      preStr  <- astToString pre
      return $ start ++ "E " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTAbduction sat interpLines pre post -> do
      rest    <- ppVTrace' indent ts
      return $ start ++ (if sat then "O " else "X ")
        ++ "<Abduction> " ++ pre ++ " -> " ++ post
        ++ (concat $ map (\line -> "\n" ++ start ++ "  :" ++ line) interpLines)
        ++ "\n" ++ rest
    VTCall kind pre fpre -> do
      rest    <- ppVTrace' indent ts
      return $ start ++ (kindStr kind) ++ ":: Precondition Check: "
        ++ pre ++ " -> " ++ fpre
        ++ "\n" ++ rest
    VTStartBranch cond -> do
      rest <- ppVTrace' (indent + 1) ts
      return $ start ++ "+ Branch: " ++ cond ++ "\n" ++ rest
    VTEndBranch -> do
      rest <- ppVTrace' (indent - 1) ts
      return $ (concat $ replicate (indent - 1) "| ") ++ "-\n" ++ rest
    VTMessage kind msg -> do
      rest <- ppVTrace' indent ts
      return $ start ++ (kindStr kind) ++ ":: " ++ msg ++ "\n" ++ rest
  where
    start = (concat $ replicate indent "| ")

ppStmtsStart :: [Stmt] -> Z3 String
ppStmtsStart [] = return "<No Programs>"
ppStmtsStart (stmt:_) = ppStmtStart stmt

ppStmtStart :: Stmt -> Z3 String
ppStmtStart stmt =
  case stmt of
    SSkip -> return "Skip"
    SAsgn var aexp -> do
      aexpStr <- astToString =<< aexpToZ3 aexp
      return $ var ++ " := " ++ aexpStr
    SSeq [] -> return "Seq []"
    SSeq (s:[]) -> ppStmtStart s
    SSeq (s:ss) -> do
      first <- ppStmtStart s
      return $ first ++ "..."
    SIf b s1 s2 -> do
      condStr <- astToString =<< bexpToZ3 b
      thenStr <- ppStmtStart s1
      elseStr <- ppStmtStart s2
      return $ "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
    SWhile cond body _ -> do
      condStr <- astToString =<< bexpToZ3 cond
      bodyStr <- ppStmtStart body
      return $ "while " ++ condStr ++ " do " ++ bodyStr ++ " end"
    SCall assignees cparams fname -> do
      let astr = "(" ++ (intercalate ", " assignees) ++ ")"
      return $ astr ++ " := " ++ fname ++ "(" ++ (intercalate ", " cparams) ++ ")"

kindStr :: VTKind -> String
kindStr VTKindA = "A"
kindStr VTKindE = "E"
kindStr VTKindGeneral = ""
