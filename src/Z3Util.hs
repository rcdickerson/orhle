module Z3Util
  ( checkSat
  , checkValid
  , subAST
  ) where

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
