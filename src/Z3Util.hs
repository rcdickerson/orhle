module Z3Util
  ( checkCSat
  , checkSat
  , checkCValid
  , checkValid
  ) where

import Conditions
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

checkCValid :: Cond -> Z3 Bool
checkCValid cond = condToZ3 cond >>= checkSat

checkCSat :: Cond -> Z3 Bool
checkCSat cond = condToZ3 cond >>= checkSat
