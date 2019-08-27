module Z3Util
  ( checkSat
  , checkValid
  , distList
  , parseSMT
  , smtString
  ) where

import Control.Monad (liftM2)
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

parseSMT :: String -> Z3 AST
parseSMT str = parseSMTLib2String str [] [] [] []

smtString :: AST -> Z3 String
smtString = astToString

-- Useful for turning [Z3 Foo] into Z3 [Foo].
distList :: Monad m => [m a] -> m [a]
distList [] = return []
distList (x:xs) = (liftM2 (:)) x (distList xs)
