module Abduction
    ( abduce
    , Abducible(..)
    , Abduction
    , emptyIMap
    , imapInit
    , imapStrengthen
    , imapUnion
    , InterpMap
    , InterpResult(..)
    , ppInterpMap
    , putInterpMap
    , singletonIMap
    ) where

import Control.Monad
import Conditions
import Imp
import qualified Data.Map as Map
import Z3.Monad

data Abducible = Abducible
  { func     :: UFunc
  , assignee :: Var
  } deriving (Eq, Ord, Show)


-------------------------
-- Interpretation Maps --
-------------------------

type InterpMap = Map.Map Abducible AST
emptyIMap = Map.empty
singletonIMap var duc = Map.singleton var duc

putInterpMap :: InterpMap -> IO ()
putInterpMap imap = mapM_ putInterpLine (Map.toList imap)
  where putInterpLine = \(duc, ast) -> do
          let ducName = fName.func $ duc
          interp <- evalZ3 $ astToString ast
          putStrLn $ "  " ++ ducName ++ ": " ++ interp

ppInterpMap :: InterpMap -> Z3 [String]
ppInterpMap imap = mapM line (Map.toList imap)
  where line = \(duc, ast) -> do
          let ducName = fName.func $ duc
          interp <- astToString ast
          return $ ducName ++ ": " ++ interp

data InterpResult = IRSat InterpMap
                  | IRUnsat
                  deriving(Show)

imapInit :: Prog -> Z3 InterpMap
imapInit prog =
  case prog of
    Skip          -> return $ emptyIMap
    Seq []        -> imapInit Skip
    Seq (s:ss)    -> do
                     first <- imapInit s
                     rest  <- imapInit $ Seq ss
                     return $ Map.union first rest
    var := aexp   -> return $ emptyIMap
    If bexp s1 s2 -> do
                     first  <- imapInit s1
                     second <- imapInit s2
                     return $ Map.union first second
    Call var f    -> do
                     initPostCond <- condToZ3.fPostCond $ f
                     -- TODO: Need to make the name unique for callsite...
                     callsiteFun <- mkFreshFuncDecl (fName f) [] =<< mkIntSort
                     return $ Map.insert (Abducible f var) initPostCond emptyIMap

imapUnion :: InterpMap -> InterpMap -> Z3 InterpMap
imapUnion imap1 imap2 = do return $ Map.union imap1 imap2 -- TODO: Need actual abduced union

imapStrengthen :: Cond -> InterpMap -> Cond -> Z3 InterpResult
imapStrengthen pre imap post = do
  let keys = Map.keys imap
  let assignees = map assignee keys
  freshVars <- mapM (\v -> mkFreshIntVar v >>= astToString >>= \f -> return (v, f)) assignees
  let subFresh = \pre' (v, f) -> csubst pre' v (V f)
  preZ3 <- condToZ3 $ foldl subFresh pre freshVars
  postZ3 <- condToZ3 post
  abduce (keys, [preZ3], postZ3:(Map.elems imap))


---------------
-- Abduction --
---------------

type Abduction = ([Abducible], [AST], [AST])

abduce :: Abduction -> Z3 InterpResult
abduce ([], pres, posts) = do
  presConj  <- mkAnd pres
  postsConj <- mkAnd posts
  noAbduction presConj postsConj
abduce (duc : [], pres, posts) = do
  presConj  <- mkAnd pres
  postsConj <- mkAnd posts
  singleAbduction duc presConj postsConj
abduce _ = error "Multi-abduction is currently unsupported!"

astVars :: AST -> Z3 [Symbol]
astVars ast = do -- TODO: Clean this up, use Set to avoid duplicates
  isFuncApp <- isApp ast
  if not isFuncApp
    then return []
    else do
      app <- toApp ast
      numArgs <- getAppNumArgs app
      if numArgs == 0
        then do
          validVar <- isVar ast
          if not validVar
            then return []
            else do
              declName <- getDeclName =<< getAppDecl app
              return [declName]
        else do
          args <- getAppArgs app
          vars <- mapM astVars args
          return $ concat vars

isVar :: AST -> Z3 Bool
isVar ast = do
  name <- astToString ast
  kind <- getAstKind ast
  let nameOk = hasVarishName name
  case kind of
    Z3_APP_AST       -> return nameOk
    Z3_FUNC_DECL_AST -> return nameOk
    Z3_VAR_AST       -> return nameOk
    _                -> return False

-- This is super hacky, but I don't see another way to
-- distinguish actual variables in Z3.
hasVarishName :: String -> Bool
hasVarishName "true" = False
hasVarishName "false" = False
hasVarishName _ = True

abducibleVars :: Abducible -> [Var]
abducibleVars (Abducible func assignee) = assignee:(fParams func)

filterVars :: [Symbol] -> [Var] -> Z3 [Symbol]
filterVars symbols vars = do
  symbolStrs <- mapM getSymbolString symbols
  let notInVars = not.(flip elem) vars
  let filteredStrs = filter notInVars symbolStrs
  mapM mkStringSymbol filteredStrs

noAbduction :: AST -> AST -> Z3 InterpResult
noAbduction conds post = do
  consistencyCheck <- satisfiable conds
  if not consistencyCheck
    then return IRUnsat
    else do
      imp <- mkImplies conds post
      vars <- astVars imp
      sat <- satisfiable =<< performQe vars imp
      if sat
        then return $ IRSat emptyIMap
        else return IRUnsat

singleAbduction :: Abducible -> AST -> AST -> Z3 InterpResult
singleAbduction duc conds post = do
  consistencyCheck <- satisfiable conds
  if not consistencyCheck
    then return IRUnsat
    else do
      fPost <- condToZ3.fPostCond.func $ duc
      imp   <- mkImplies conds =<< mkAnd [fPost, post]
      vars  <- astVars imp
      vbar  <- filterVars vars (abducibleVars duc)
      qeRes <- performQe vbar imp
      sat   <- satisfiable qeRes
      if sat
        then return $ IRSat $ Map.insert duc qeRes emptyIMap
        else return IRUnsat

performQe :: [Symbol] -> AST -> Z3 AST
performQe vars formula = do
  intVars <- mapM mkIntVar vars
  appVars <- mapM toApp intVars
  qf <- mkForallConst [] appVars formula
  goal <- mkGoal False False False
  goalAssert goal qf
  qe <- mkTactic "qe"
  qeResult <- applyTactic qe goal
  subgoals <- getApplyResultSubgoals qeResult
  formulas <- mapM getGoalFormulas subgoals
  mkAnd $ concat formulas

satisfiable :: AST -> Z3 Bool
satisfiable ast = do
  push
  assert ast
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False
