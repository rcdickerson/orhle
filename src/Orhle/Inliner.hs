--
-- Inlines all implemented function bodies into a given block of code. Fails if
-- the program contains recursion.
--
module Orhle.Inliner
  ( inline
  ) where

import Orhle.Imp
import Orhle.Names

type Error = String

inline :: Program -> FunImplEnv -> Either Error Program
inline prog impls = do
  return prog
