module RHLE
  ( mkRHLETrip
  , RHLETrip(..)
  ) where

import Imp
import SMTParser
import Z3.Monad

data RHLETrip = RHLETrip
  { rhlePre   :: AST
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost  :: AST
  } deriving (Show)

mkRHLETrip :: String -> Prog -> Prog -> String -> Z3 RHLETrip
mkRHLETrip pre progA progE post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ RHLETrip preAST progA progE postAST
