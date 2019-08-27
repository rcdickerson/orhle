module VTrace
  ( logAbductionFailure
  , logAbductionSuccess
  , logBranchEnd
  , logBranchStart
  , logCallA
  , logCallE
  , logHle
  , logMsgA
  , logMsgE
  , logRhle
  , ppVTrace
  , VTrace
  , VTWriter
  ) where

import Control.Monad.Writer
import Data.List
import HoareE
import Imp
import RHLE
import Z3.Monad
import Z3Util

data VTrace = VTRhle RHLETrip
            | VTHle  HLETrip
            | VTAbduction Bool [String] String String
            | VTCall VTKind String String
            | VTStartBranch String
            | VTEndBranch
            | VTMessage VTKind String

data VTKind = VTKindA | VTKindE

type VTWriter m a = WriterT [VTrace] m a

logRhle :: (Monad m) => RHLETrip -> VTWriter m ()
logRhle trip = do tell [VTRhle trip]

logHle :: (Monad m) => HLETrip -> VTWriter m ()
logHle trip = do tell [VTHle trip]

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

ppVTrace :: [VTrace] -> Z3 String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VTrace] -> Z3 String
ppVTrace' _ [] = return ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre progA progE post) -> do
      progStr <- ppStmtStart progA
      rest    <- ppVTrace' indent ts
      preStr  <- smtString pre
      return $ start ++ "A " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTHle  (HLETrip  pre progE post) -> do
      progStr <- ppStmtStart progE
      rest    <- ppVTrace' indent ts
      preStr  <- smtString pre
      return $ start ++ "E " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTAbduction sat interpLines pre post -> do
      rest    <- ppVTrace' indent ts
      return $ start ++ (if sat then "O " else "X ")
        ++ "<Abduction> " ++ pre ++ " -> " ++ post
        ++ (concat $ map (\line -> "\n" ++ start ++ "  :" ++ line) interpLines)
        ++ "\n" ++ rest
    VTCall kind pre fpre -> do
      rest    <- ppVTrace' indent ts
      return $ start ++ (kindStr kind) ++ " :: Precondition Check: "
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
      return $ start ++ (kindStr kind) ++ " :: " ++ msg ++ "\n" ++ rest
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
      condStr <- astToString =<< bexpToZ3 b
      thenStr <- ppStmtStart s1
      elseStr <- ppStmtStart s2
      return $ "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
    Call v (UFunc name params pre post) -> do
      return $ v ++ " := " ++ name ++ "(" ++ (intercalate ", " params) ++ ")"

kindStr :: VTKind -> String
kindStr VTKindA = "A"
kindStr VTKindE = "E"
