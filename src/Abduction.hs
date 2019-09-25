module Abduction
    ( Abducible(..)
    , AbductionResult
    , abduce
    ) where

import AbdTrace
import Abducible
import Control.Monad.Trans
import Control.Monad.Writer
import Data.Foldable
import qualified Data.Map as Map
import qualified Data.Set as Set
import Imp
import InterpMap
import MSA
import Simplify
import Z3.Monad
import Z3Util

--------------------------------------------------------------------------------

data AbductionProblem = AbductionProblem
  { apAbducibles :: [Abducible]
  , apPreCond    :: AST
  , apPostCond   :: AST
  } deriving (Show)

type AbductionResult = Either String InterpMap
type TracedResult    = ATWriter Z3 AbductionResult

--------------------------------------------------------------------------------

abduce :: [Abducible] -> [AST] -> [AST] -> Z3 (AbductionResult, [AbdTrace])
abduce abds pres posts = do
  pre  <- mkAnd pres
  post <- mkAnd posts
  runWriterT $ tracedAbduce =<< flatten (AbductionProblem abds pre post)

tracedAbduce :: AbductionProblem -> TracedResult
tracedAbduce (AbductionProblem abds pre post) = do
  logAbdStart (map show abds) pre post
  consistencyCheck <- lift $ checkSat pre
  if not consistencyCheck
    then (\msg -> logAbdFailure msg >>= (return.return.Left $ msg))
      "Preconditions are not consistent."
    else case abds of
        []     -> noAbduction          pre post
        abd:[] -> singleAbduction abd  pre post
        _      -> multiAbduction  abds pre post

flatten :: AbductionProblem -> ATWriter Z3 AbductionProblem
flatten (AbductionProblem abds pre post) = do
  freshVarMap <- lift $ fvmFromAbducibles abds
  pre'        <- lift $ fvmFlatten freshVarMap pre
  post'       <- lift $ fvmFlatten freshVarMap post
  logAbdFlatten "Precond" pre pre' >> logAbdFlatten "Postcond" post post'
  return $ AbductionProblem (Set.toList $ fvmFreshAbds freshVarMap) pre' post'

filterVars :: [Symbol] -> [Var] -> Z3 [Symbol]
filterVars symbols vars = do
  symbolStrs <- mapM getSymbolString symbols
  let notInVars = not.(flip elem) vars
  let filteredStrs = filter notInVars symbolStrs
  mapM mkStringSymbol filteredStrs

noAbduction :: AST -> AST -> TracedResult
noAbduction pre post = do
  logAbdMessage "No variables to abduce over; using simplified pre => post."
  imp   <- lift $ mkImplies pre post
  simpl <- lift $ simplifyWrt pre imp
  logAbdFormula "Simplified implication" simpl
  sat   <- lift $ checkSat simpl
  if sat
    then return.Right $ emptyIMap
    else return.Left  $ "Preconditions are inconsistent with postconditions."

singleAbduction :: Abducible -> AST -> AST -> TracedResult
singleAbduction abd@(Abducible abdName abdParams) pre post = do
  logAbdMessage $ "Performing single abduction for " ++ abdName
  imp        <- lift $ mkImplies pre post
  logAbdFormula "Initial implication" imp
  freeVars    <- lift $ astFreeVars imp
  freeVarStrs <- lift $ sequence $ map getSymbolString freeVars
  logAbdMessage $ "Formula variables: " ++ (show freeVarStrs)
  vbar       <- lift $ filterVars freeVars abdParams
  vbarStrs   <- lift $ symbolsToStrings vbar
  logAbdMessage $ "Candidate variables for MUS: " ++ (show vbarStrs)
  musVars    <- lift $ findMusVars imp vbar
  musVarStrs <- lift $ symbolsToStrings musVars
  logAbdMessage $ "MUS Vars: " ++ (show musVarStrs)
  qeRes      <- lift $ performQe musVars imp
  logAbdFormula "QE Result" qeRes
  qeResSimpl <- lift $ simplifyWrt pre qeRes
  logAbdFormula "Simplified QE Result" qeResSimpl
  sat        <- lift $ checkSat qeResSimpl
  case sat of
    False -> return.Left  $ "No satisfying abduction found."
    True  -> return.Right $ Map.insert abd qeResSimpl emptyIMap

multiAbduction :: [Abducible] -> AST -> AST -> TracedResult
multiAbduction abds pre post = do
  logAbdMessage $ "Performing multiabduction over " ++ (show $ map abdName abds)
  combinedAbd    <- lift $ combineAbducibles abds
  combinedResult <- singleAbduction combinedAbd pre post
  case combinedResult of
    Left  err  -> return.Left $ err
    Right imap -> cartDecomp abds pre (imap Map.! combinedAbd)

combineAbducibles :: [Abducible] -> Z3 Abducible
combineAbducibles abds = do
  let vars = foldr insertAbd Set.empty abds
  return $ Abducible "_combined_abducible" $ Set.toList vars
    where insertAbd (Abducible _ vars) varSet = foldr Set.insert varSet vars

cartDecomp :: [Abducible] -> AST -> AST -> TracedResult
cartDecomp abds pre combinedResult = do
  logAbdMessage "! Cartesian Decomposition"
  logAbdMessage $ "Abducibles: " ++ (show abds)
  logAbdFormula "Precondition" pre
  logAbdFormula "Combined Result" combinedResult
  initMap <- lift $ initSolution abds pre combinedResult
  foldlM (replaceWithDecomp combinedResult) initMap abds
  where
    replaceWithDecomp :: AST -> AbductionResult -> Abducible -> TracedResult
    replaceWithDecomp _    (Left err)   _   = return.Left $ err
    replaceWithDecomp post (Right imap) abd = do
      decResult <- (decompose post) abd imap
      case decResult of
        Left  err -> return.Left  $ err
        Right dec -> return.Right $ Map.union dec imap
    decompose :: AST -> Abducible -> InterpMap -> TracedResult
    decompose post abd imap = do
      let complement = Map.withoutKeys imap $ Set.singleton abd
      pre' <- lift $ mkAnd (map snd $ Map.toList complement)
      ires <- tracedAbduce $ AbductionProblem [abd] pre' post
      case ires of
        Left  err   -> return.Left $
          "Unable to decompose " ++ (show combinedResult) ++ ": " ++ err
        Right imap' -> return.Right $ imap'

initSolution :: [Abducible] -> AST -> AST -> Z3 AbductionResult
initSolution abds pre combinedResult = do
  modelRes <- modelAST =<< mkAnd [pre, combinedResult]
  case modelRes of
    Left  err   -> return.Left $ err
    Right model -> foldlM (getAbdInterp model) (Right Map.empty) abds
  where
    getAbdInterp :: Model -> AbductionResult -> Abducible -> Z3 AbductionResult
    getAbdInterp _     (Left  err)  _   = return.Left $ err
    getAbdInterp model (Right imap) abd = do
      varInterps <- mapM (getVarInterp model) (abdParams abd)
      case foldr eitherCons (Right []) varInterps of
        Left err -> return.Left $ err
        Right asts -> do
          interp <- mkAnd asts
          return.Right $ Map.insert abd interp imap
    ----
    eitherCons :: (Either String AST) -> (Either String [AST]) -> (Either String [AST])
    eitherCons (Left err)  _           = Left err
    eitherCons _           (Left err)  = Left err
    eitherCons (Right ast) (Right lst) = Right (ast:lst)
    ----
    getVarInterp :: Model -> Var -> Z3 (Either String AST)
    getVarInterp model var = do
      varSymb <- mkStringSymbol $ var
      varDecl <- mkFuncDecl varSymb [] =<< mkIntSort
      interp  <- getConstInterp model varDecl
      case interp of
        Nothing -> return.Left  $  "Unable to model value for " ++ var
        Just v  -> return.Right =<< mkEq v =<< aexpToZ3 (V $ var)


performQe :: [Symbol] -> AST -> Z3 AST
performQe [] formula = return formula
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
