module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  ) where

import Orhle.Assertion
import Orhle.Imp

data HlTriple = HlTriple
  { hlPre  :: Assertion
  , hlProg :: Stmt
  , hlPost :: Assertion
  } deriving (Show)

data HleTriple = HleTriple
  { hlePre  :: Assertion
  , hleProg :: Stmt
  , hlePost :: Assertion
  } deriving (Show)

data RhleTriple = RhleTriple
  { rhlePre    :: Assertion
  , rhleAProgs :: [Stmt]
  , rhleEProgs :: [Stmt]
  , rhlePost   :: Assertion
  } deriving (Show)
