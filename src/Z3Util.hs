module Z3Util
  ( astFreeVars
  , checkSat
  , checkValid
  , mkFreshIntVars
  , getModelAsString
  , substituteByName
  , symbolsToStrings
  ) where

import Control.Monad (foldM)
import Data.List
import qualified Data.Set as Set
import Z3.Monad

checkValid :: AST -> Z3 Bool
checkValid ast = do
  negSat <- checkSat =<< mkNot ast
  return $ not negSat

checkSat :: AST -> Z3 Bool
checkSat ast = do
  result <- solverCheckAssumptions [ast]
  case result of
    Sat -> return True
    _   -> return False

getModelAsString :: AST -> Z3 String
getModelAsString ast = do
  push
  assert ast
  res <- getModel
  pop 1
  case res of
    (Sat, Just model) -> showModel model
    _                 -> return "<< Unable to model >>"

symbolsToStrings :: [Symbol] -> Z3 [String]
symbolsToStrings syms = sequence $ map getSymbolString syms

substituteByName :: AST -> [String] -> [String] -> Z3 AST
substituteByName ast fromStrings toStrings = do
  fromSymbols <- mapM mkStringSymbol fromStrings
  toSymbols   <- mapM mkStringSymbol toStrings
  fromASTs    <- mapM mkIntVar fromSymbols
  toASTs      <- mapM mkIntVar toSymbols
  substitute ast fromASTs toASTs

astFreeVars :: AST -> Z3 [Symbol]
astFreeVars ast = do
  vars <- astFreeVars' ast Set.empty Set.empty
  return $ Set.toList vars

astFreeVars' :: AST -> (Set.Set Symbol) -> (Set.Set Symbol) -> Z3 (Set.Set Symbol)
astFreeVars' ast boundVars freeVars = do
  astIsApp    <- isApp ast
  astIsExists <- isQuantifierExists ast
  astIsForall <- isQuantifierForall ast
  case (astIsApp, astIsExists || astIsForall) of
    (False, False) -> return freeVars
    (True, _)  -> do
      app      <- toApp ast
      numArgs  <- getAppNumArgs app
      case numArgs of
        0 -> do
          astIsVar <- isVar ast
          varSymb <- getDeclName =<< getAppDecl app
          return $ if (varSymb `Set.member` boundVars) || (not astIsVar)
                      then freeVars
                      else (Set.insert) varSymb freeVars
        _ -> do
          appArgs <- getAppArgs app
          foldM (\free' arg -> astFreeVars' arg boundVars free') freeVars appArgs
    (_, True) -> do
      numBound <- getQuantifierNumBound ast
      bound    <- sequence $ map (\i -> getQuantifierBoundName ast i) [0..numBound-1]
      body     <- getQuantifierBody ast
      astFreeVars' body (foldr Set.insert boundVars bound) freeVars

isVar :: AST -> Z3 Bool
isVar ast = do
  astStr <- astToString ast
  case stripPrefix "(:var " astStr of
    Just _ -> return True
    _      -> do
      astIsApp <- isApp ast
      if not astIsApp then return True else do
        app     <- toApp ast
        arity   <- getAppNumArgs app
        boolLit <- isBoolLit ast
        if arity > 0 then return False else do
          kind <- getAstKind ast
          case kind of
            Z3_APP_AST  -> return $ not boolLit
            _           -> return False

-- This is super hacky, but I don't see another way to
-- distinguish variables from boolean literals.
isBoolLit :: AST -> Z3 Bool
isBoolLit ast = do
  astStr <- astToString ast
  return $ astStr `elem` ["true", "false"]

mkFreshIntVars :: [String] -> Z3 [AST]
mkFreshIntVars vars = mapM mkFreshIntVar vars
