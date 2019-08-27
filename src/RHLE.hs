module RHLE
  ( mkRHLETrip
  , RHLETrip(..)
  ) where

import Imp
import Z3.Monad
import Z3Util

data RHLETrip = RHLETrip
  { rhlePre   :: AST
  , rhleProgA :: Prog
  , rhleProgE :: Prog
  , rhlePost  :: AST
  } deriving (Show)

mkRHLETrip :: String -> Prog -> Prog -> String -> Z3 RHLETrip
mkRHLETrip pre progA progE post = do
  preAST  <- parseSMT pre
  postAST <- parseSMT post
  return $ RHLETrip preAST progA progE postAST
