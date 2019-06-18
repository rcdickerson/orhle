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

import Conditions
import Control.Monad.Writer
import Data.List
import HoareE
import Imp
import RHLE
import Z3.Monad

data VTrace = VTRhle RHLETrip
            | VTHle  HLETrip
            | VTAbduction Bool [String] Cond Cond
            | VTCall VTKind Cond Cond
            | VTStartBranch Cond
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

logBranchStart :: (Monad m) => Cond -> VTWriter m ()
logBranchStart cond = do tell [VTStartBranch cond]

logBranchEnd :: (Monad m) => VTWriter m ()
logBranchEnd = do tell [VTEndBranch]

logAbductionSuccess :: (Monad m) => [String] -> Cond -> Cond -> VTWriter m ()
logAbductionSuccess interpLines pre post = do
  tell [VTAbduction True interpLines pre post]

logAbductionFailure :: (Monad m) => Cond -> Cond -> VTWriter m ()
logAbductionFailure pre post = do
  tell [VTAbduction False [] pre post]

logCallA :: (Monad m) => Cond -> Cond -> VTWriter m ()
logCallA pre post = do tell [VTCall VTKindA pre post]

logCallE :: (Monad m) => Cond -> Cond -> VTWriter m ()
logCallE pre post = do tell [VTCall VTKindE pre post]

ppVTrace :: [VTrace] -> Z3 String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VTrace] -> Z3 String
ppVTrace' _ [] = return ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre progA progE post) -> do
      preStr <- condZ3String pre
      progStr <- ppStmtStart progA
      rest   <- ppVTrace' indent ts
      return $ start ++ "A " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTHle  (HLETrip  pre progE post) -> do
      preStr  <- condZ3String pre
      progStr <- ppStmtStart progE
      rest    <- ppVTrace' indent ts
      return $ start ++ "E " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTAbduction sat interpLines pre post -> do
      preStr  <- condZ3String pre
      postStr <- condZ3String post
      rest    <- ppVTrace' indent ts
      return $ start ++ (if sat then "O " else "X ")
        ++ "<Abduction> " ++ preStr ++ " -> " ++ postStr
        ++ (concat $ map (\line -> "\n" ++ start ++ "  :" ++ line) interpLines)
        ++ "\n" ++ rest
    VTCall kind pre fpre -> do
      preStr  <- condZ3String pre
      fPreStr <- condZ3String fpre
      rest    <- ppVTrace' indent ts
      return $ start ++ (kindStr kind) ++ " :: Precondition Check: "
        ++ preStr ++ " -> " ++ fPreStr
        ++ "\n" ++ rest
    VTStartBranch cond -> do
      condStr <- condZ3String cond
      rest <- ppVTrace' (indent + 1) ts
      return $ start ++ "+ Branch: " ++ condStr ++ "\n" ++ rest
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
      condStr <- condZ3String $ bexpToCond b
      thenStr <- ppStmtStart s1
      elseStr <- ppStmtStart s2
      return $ "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
    Call v (UFunc name params pre post) -> do
      return $ v ++ " := " ++ name ++ "(" ++ (intercalate ", " params) ++ ")"

kindStr :: VTKind -> String
kindStr VTKindA = "A"
kindStr VTKindE = "E"