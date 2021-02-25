module Triples
  ( HLETrip(..)
  , HLTrip(..)
  , RHLETrip(..)
  , mkHLETrip
  , mkHLTrip
  , mkRHLETrip
  ) where

import Assertion
import AssertionParser
import Imp

data HLTrip = HLTrip
  { hlPre  :: Assertion
  , hlProg :: Stmt
  , hlPost :: Assertion
  } deriving (Show)

mkHLTrip :: String -> Stmt -> String -> Either ParseError HLTrip
mkHLTrip pre prog post = do
  preAST  <- parseAssertion pre
  postAST <- parseAssertion post
  return $ HLTrip preAST prog postAST

data HLETrip = HLETrip
  { hlePre  :: Assertion
  , hleProg :: Stmt
  , hlePost :: Assertion
  } deriving (Show)

mkHLETrip :: String -> Stmt -> String -> Either ParseError HLETrip
mkHLETrip pre prog post = do
  preAST  <- parseAssertion pre
  postAST <- parseAssertion post
  return $ HLETrip preAST prog postAST

data RHLETrip = RHLETrip
  { rhlePre    :: Assertion
  , rhleAProgs :: [Stmt]
  , rhleEProgs :: [Stmt]
  , rhlePost   :: Assertion
  } deriving (Show)

mkRHLETrip :: String -> [Stmt] -> [Stmt] -> String -> Either ParseError RHLETrip
mkRHLETrip pre aProgs eProgs post = do
  preAST  <- parseAssertion pre
  postAST <- parseAssertion post
  return $ RHLETrip preAST aProgs eProgs postAST
