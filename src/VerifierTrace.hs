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

import           Control.Monad.Writer
import qualified Data.List            as List
import           Imp
import           ImpPrettyPrint
import           Triples
import qualified SMTMonad as SMT

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

ppVTrace :: [VerifierTrace] -> String
ppVTrace = ppVTrace' 0

ppVTrace' :: Int -> [VerifierTrace] -> String
ppVTrace' _ [] = ""
ppVTrace' indent (t:ts) =
  case t of
    VTRhle (RHLETrip pre aProgs eProgs post) ->
      let progStr = ppStmtsStart aProgs
          rest    = ppVTrace' indent ts
          preStr  = SMT.exprToString pre
      in start ++ "A " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTHle  (HLETrip  pre progE post) ->
      let progStr = ppStmtStart progE
          rest    = ppVTrace' indent ts
          preStr  = SMT.exprToString pre
      in start ++ "E " ++ preStr ++ " :: " ++ progStr ++ "\n" ++ rest
    VTAbduction sat interpLines pre post ->
      let rest    = ppVTrace' indent ts
      in start ++ (if sat then "O " else "X ")
        ++ "<Abduction> " ++ pre ++ " -> " ++ post
        ++ (concat $ map (\line -> "\n" ++ start ++ "  :" ++ line) interpLines)
        ++ "\n" ++ rest
    VTCall kind pre fpre ->
      let rest    = ppVTrace' indent ts
      in start ++ (kindStr kind) ++ ":: Precondition Check: "
        ++ pre ++ " -> " ++ fpre
        ++ "\n" ++ rest
    VTStartBranch cond ->
      let rest = ppVTrace' (indent + 1) ts
      in start ++ "+ Branch: " ++ cond ++ "\n" ++ rest
    VTEndBranch ->
      let rest = ppVTrace' (indent - 1) ts
      in (concat $ replicate (indent - 1) "| ") ++ "-\n" ++ rest
    VTMessage kind msg ->
      let rest = ppVTrace' indent ts
      in start ++ (kindStr kind) ++ ":: " ++ msg ++ "\n" ++ rest
  where
    start = (concat $ replicate indent "| ")

ppStmtsStart :: [Stmt] -> String
ppStmtsStart [] = "<No Programs>"
ppStmtsStart (stmt:_) = ppStmtStart stmt

ppStmtStart :: Stmt -> String
ppStmtStart stmt =
  case stmt of
    SSkip -> "Skip"
    SAsgn var aexp ->
      let aexpStr = prettyprintAExp aexp
      in var ++ " := " ++ aexpStr
    SSeq [] -> "Seq []"
    SSeq (s:[]) -> ppStmtStart s
    SSeq (s:ss) ->
      let first = ppStmtStart s
      in first ++ "..."
    SIf b s1 s2 ->
      let condStr = prettyprintBExp b
          thenStr = ppStmtStart s1
          elseStr = ppStmtStart s2
      in "if " ++ condStr ++ " then " ++ thenStr ++ " else " ++ elseStr
    SWhile cond body _ ->
      let condStr = prettyprintBExp cond
          bodyStr = ppStmtStart body
      in "while " ++ condStr ++ " do " ++ bodyStr ++ " end"
    SCall assignees cparams fname ->
      let astr = "(" ++ (List.intercalate ", " assignees) ++ ")"
      in astr ++ " := " ++ fname ++ "(" ++ (List.intercalate ", " cparams) ++ ")"

kindStr :: VTKind -> String
kindStr VTKindA = "A"
kindStr VTKindE = "E"
kindStr VTKindGeneral = ""
