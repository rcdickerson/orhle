module Triples
  ( HLETrip(..)
  , HLTrip(..)
  , RHLETrip(..)
  , mkHLETrip
  , mkHLTrip
  , mkRHLETrip
  ) where

import Imp
import SMTParser
import Z3.Monad

data HLTrip = HLTrip
  { hlPre  :: AST
  , hlProg :: Prog
  , hlPost :: AST
  } deriving (Show)

mkHLTrip :: String -> Prog -> String -> Z3 HLTrip
mkHLTrip pre prog post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ HLTrip preAST prog postAST

data HLETrip = HLETrip
  { hlePre  :: AST
  , hleProg :: Prog
  , hlePost :: AST
  } deriving (Show)

mkHLETrip :: String -> Prog -> String -> Z3 HLETrip
mkHLETrip pre prog post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ HLETrip preAST prog postAST

data RHLETrip = RHLETrip
  { rhlePre    :: AST
  , rhleAProgs :: [Prog]
  , rhleEProgs :: [Prog]
  , rhlePost   :: AST
  } deriving (Show)

mkRHLETrip :: String -> [Prog] -> [Prog] -> String -> Z3 RHLETrip
mkRHLETrip pre aProgs eProgs post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ RHLETrip preAST aProgs eProgs postAST
