module Z3Util
  ( astFreeVars
  , checkSat
  , checkValid
  , mkFreshIntVars
  , maybeModelToString
  , prefixASTVars
  , stringsToApps
  , substituteByName
  , symbolsToStrings
  ) where

import Control.Monad (foldM)
import Data.List
import qualified Data.Set as Set
import Z3.Monad

checkValid :: AST -> Z3 (Bool, Maybe Model)
checkValid ast = do
  (negSat, model) <- checkSat =<< mkNot ast
  return (not negSat, model)

checkSat :: AST -> Z3 (Bool, Maybe Model)
checkSat ast = do
  push
  assert ast
  result <- getModel
  pop 1
  case result of
    (Sat, model) -> return (True, model)
    (_  , model) -> return (False, model)

maybeModelToString :: Maybe Model -> Z3 String
maybeModelToString Nothing = return "<< Unable to model >>"
maybeModelToString (Just model) = showModel model

symbolsToStrings :: [Symbol] -> Z3 [String]
symbolsToStrings syms = sequence $ map getSymbolString syms

stringsToApps :: [String] -> Z3 [App]
stringsToApps = mapM $ \s -> toApp =<< mkIntVar =<< mkStringSymbol s

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

prefixASTVars :: String -> AST -> Z3 AST
prefixASTVars prefix ast = do
  vars <- symbolsToStrings =<< astFreeVars ast
  let pvars = map (\v -> prefix ++ v) vars
  substituteByName ast vars pvars
