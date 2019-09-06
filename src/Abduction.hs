module Abduction
    ( AbductionProblem
    , AbductionResult
    , abduce
    , imapStrengthen
    ) where

import Control.Monad (foldM)
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Imp
import InterpMap
import Simplify
import Z3.Monad
import Z3Util

type AbductionProblem = ([Var], [AST], [AST])
type AbductionResult  = Either String InterpMap

imapStrengthen :: AST -> InterpMap -> AST -> Z3 AbductionResult
imapStrengthen pre imap post = do
  let vars  = Map.keys imap
  freshPre <- foldM (\pre' -> uncurry $ subVar pre') pre =<< mapM freshen vars
  abduce (vars, [freshPre], post:(Map.elems imap))
  where
    -- Fresh vars in the precondition effectively "forget" what we know
    -- about the variables in the interpretation map. This ensures the
    -- abduced replacement interpretations are sufficiently strong.
    freshen v = mkFreshIntVar v >>= astToString >>= \fresh -> return (v, fresh)

abduce :: AbductionProblem -> Z3 AbductionResult
abduce (vars, pres, posts) = do
  consistencyCheck <- checkSat =<< mkAnd pres
  if not consistencyCheck
    then return.Left $ "Preconditions are not consistent."
    else do
      result <- case vars of
        []     -> noAbduction               pres posts
        var:[] -> singleAbduction var [var] pres posts
        _      -> multiAbduction  vars      pres posts
      return result

astVars :: AST -> Z3 [Symbol]
astVars ast = do
  astIsApp <- isApp ast
  case astIsApp of
    False -> return []
    True  -> do
      app      <- toApp ast
      astIsVar <- isVar ast
      numArgs  <- getAppNumArgs app
      case (numArgs, astIsVar) of
        (0, False) -> return []
        (0, True ) -> return . (:[]) =<< getDeclName =<< getAppDecl app
        _          -> appVars app
  where
    appVars :: App -> Z3 [Symbol]
    appVars app = do
      args <- getAppArgs app
      vars <- mapM astVars args
      let dedup = Set.toList . Set.fromList
      return . dedup . concat $ vars

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
hasVarishName s = not.elem s $ ["true", "false"]

filterVars :: [Symbol] -> [Var] -> Z3 [Symbol]
filterVars symbols vars = do
  symbolStrs <- mapM getSymbolString symbols
  let notInVars = not.(flip elem) vars
  let filteredStrs = filter notInVars symbolStrs
  mapM mkStringSymbol filteredStrs

noAbduction :: [AST] -> [AST] -> Z3 AbductionResult
noAbduction conds posts = do
  condAST <- mkAnd conds
  postAST <- mkAnd posts
  imp     <- mkImplies condAST postAST
  vars    <- astVars imp
  sat     <- checkSat =<< performQe vars imp
  if sat
    then return.Right $ emptyIMap
    else return.Left  $ "Preconditions do not imply postconditions."

singleAbduction :: String -> [Var] -> [AST] -> [AST]
                -> Z3 AbductionResult
singleAbduction name vars conds posts = do
  condAST    <- mkAnd conds
  postAST    <- mkAnd posts
  imp        <- mkImplies condAST postAST
  impVars    <- astVars imp
  vbar       <- filterVars impVars vars
  qeRes      <- performQe vbar imp
  qeResSimpl <- simplifyWrt condAST qeRes
  sat        <- checkSat qeResSimpl
  case sat of
    False -> return.Left $ "No satisfying abduction found."
    True  -> return.Right $ Map.insert name qeResSimpl emptyIMap

multiAbduction :: [Var] -> [AST] -> [AST] -> Z3 AbductionResult
multiAbduction vars conds posts = do
  let combinedDuc = "_combined"
  combinedResult <- singleAbduction combinedDuc vars conds posts
  case combinedResult of
    Left  err  -> return.Left $ err
    Right imap -> cartDecomp vars conds (imap Map.! combinedDuc)

cartDecomp :: [Var] -> [AST] -> AST -> Z3 AbductionResult
cartDecomp vars conds combinedResult = do
  initMap <- initSolution vars conds combinedResult
  foldlM (replaceWithDecomp combinedResult) initMap vars
  where
    replaceWithDecomp :: AST -> AbductionResult -> Var -> Z3 AbductionResult
    replaceWithDecomp _    (Left err)   _   = return.Left $ err
    replaceWithDecomp post (Right imap) var = do
      decResult <- (decompose post) var imap
      case decResult of
        Left  err -> return.Left  $ err
        Right dec -> return.Right $ Map.union dec imap
    decompose :: AST -> Var -> InterpMap -> Z3 AbductionResult
    decompose post var imap = do
      let complement = Map.withoutKeys imap $ Set.singleton var
      ires <- abduce ([var], map snd $ Map.toList complement, [post])
      case ires of
        Left  err   -> return.Left $ "Unable to decompose " ++ (show combinedResult)
                       ++ ": " ++ err
        Right imap' -> return.Right $ imap'

initSolution :: [Var] -> [AST] -> AST -> Z3 AbductionResult
initSolution vars conds combinedResult = do
  condAST  <- mkAnd conds
  modelRes <- modelAST =<< mkAnd [condAST, combinedResult]
  case modelRes of
    Left  err   -> return.Left $ err
    Right model -> foldlM (getInterp model) (Right Map.empty) vars
  where
    getInterp :: Model -> AbductionResult -> Var -> Z3 AbductionResult
    getInterp _     (Left  err)  _   = return.Left $ err
    getInterp model (Right imap) var = do
      varSymb <- mkStringSymbol $ var
      varDecl <- mkFuncDecl varSymb [] =<< mkIntSort
      interp  <- getConstInterp model varDecl
      case interp of
        Nothing -> return.Left $ "Unable to model value for " ++ var
        Just v  -> do
          eqv <- mkEq v =<< aexpToZ3 (V $ var)
          return.Right $ Map.insert var eqv imap


performQe :: [Symbol] -> AST -> Z3 AST
performQe vars formula = do
  push
  intVars  <- mapM mkIntVar vars
  appVars  <- mapM toApp intVars
  qf       <- mkForallConst [] appVars formula
  goal     <- mkGoal False False False
  goalAssert goal qf
  qe       <- mkTactic "qe"
  qeResult <- applyTactic qe goal
  subgoals <- getApplyResultSubgoals qeResult
  formulas <- mapM getGoalFormulas subgoals
  pop 1
  mkAnd $ concat formulas

modelAST :: AST -> Z3 (Either String Model)
modelAST ast = do
  push
  assert ast
  res <- getModel
  pop 1
  case res of
    (Sat, Just model) -> return.Right $ model
    _ -> do
      astStr <- astToString ast
      return.Left $ "Unable to model " ++ astStr
