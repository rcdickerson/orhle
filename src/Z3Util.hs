module Z3Util
  ( astVars
  , checkSat
  , checkValid
  , subAST
  ) where

import qualified Data.Set as Set
import qualified Data.Text as T
import SMTParser
import Z3.Monad

checkValid :: AST -> Z3 Bool
checkValid ast = do
  push
  assert =<< mkNot ast
  result <- check
  pop 1
  case result of
    Unsat -> return True
    _     -> return False

checkSat :: AST -> Z3 Bool
checkSat ast = do
  push
  assert ast
  result <- check
  pop 1
  case result of
    Sat -> return True
    _   -> return False

subAST :: AST -> AST -> AST -> Z3 AST
subAST ast from to = do
  astStr  <- astToString ast
  fromStr <- astToString from
  toStr   <- astToString to
  let replacedStr = T.unpack $ T.replace (T.pack fromStr) (T.pack toStr) (T.pack astStr)
  parseSMTOrError replacedStr

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
