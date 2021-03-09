module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  ) where

import Orhle.Assertion
import Orhle.Imp

data HlTriple = HlTriple
  { hlPre  :: Assertion
  , hlProg :: Program
  , hlPost :: Assertion
  } deriving (Show)

data HleTriple = HleTriple
  { hlePre  :: Assertion
  , hleProg :: Program
  , hlePost :: Assertion
  } deriving (Show)

data RhleTriple = RhleTriple
  { rhlePre    :: Assertion
  , rhleAProgs :: [Program]
  , rhleEProgs :: [Program]
  , rhlePost   :: Assertion
  } deriving (Show)
