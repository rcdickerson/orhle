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
import qualified SMTMonad as S

data HLTrip = HLTrip
  { hlPre  :: S.Expr
  , hlProg :: Prog
  , hlPost :: S.Expr
  } deriving (Show)

mkHLTrip :: String -> Prog -> String -> S.SMT HLTrip
mkHLTrip pre prog post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ HLTrip preAST prog postAST

data HLETrip = HLETrip
  { hlePre  :: S.Expr
  , hleProg :: Prog
  , hlePost :: S.Expr
  } deriving (Show)

mkHLETrip :: String -> Prog -> String -> S.SMT HLETrip
mkHLETrip pre prog post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ HLETrip preAST prog postAST

data RHLETrip = RHLETrip
  { rhlePre    :: S.Expr
  , rhleAProgs :: [Prog]
  , rhleEProgs :: [Prog]
  , rhlePost   :: S.Expr
  } deriving (Show)

mkRHLETrip :: String -> [Prog] -> [Prog] -> String -> S.SMT RHLETrip
mkRHLETrip pre aProgs eProgs post = do
  preAST  <- parseSMTOrError pre
  postAST <- parseSMTOrError post
  return $ RHLETrip preAST aProgs eProgs postAST
