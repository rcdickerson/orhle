module Z3Util
  ( checkSat
  , checkValid
  , distList
  , parseSMT
  , SMTString
  , smtString
  ) where

import Control.Monad (liftM2)
import Z3.Monad

-- Keeping long-lived AST objects around seems to lead to random segfaults and
-- nonsensical Z3 errors. I suspect memory management bugs in the binding layer,
-- but have not investigated deeply.
--
-- Until I can figure out why keeping Z3 objects around for a long time is
-- leading to more crashes, the strategy is to keep SMT expressions as Strings
-- as much as possible and convert to ASTs right before an SMT query. This isn't
-- great because of the constant translation between String and AST, but is
-- better than lots of arbitrary segfaulting.
type SMTString = String

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

parseSMT :: SMTString -> Z3 AST
parseSMT str = parseSMTLib2String str [] [] [] []

smtString :: AST -> Z3 String
smtString = astToString

-- Useful for turning [Z3 Foo] into Z3 [Foo].
distList :: Monad m => [m a] -> m [a]
distList [] = return []
distList (x:xs) = (liftM2 (:)) x (distList xs)
