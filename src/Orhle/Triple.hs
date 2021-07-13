module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  ) where

import Ceili.Assertion
import Orhle.SpecImp

data HlTriple = HlTriple
  { hlPre  :: Assertion
  , hlProg :: SpecImpProgram
  , hlPost :: Assertion
  } deriving (Show)

data HleTriple = HleTriple
  { hlePre  :: Assertion
  , hleProg :: SpecImpProgram
  , hlePost :: Assertion
  } deriving (Show)

data RhleTriple = RhleTriple
  { rhlePre    :: Assertion
  , rhleAProgs :: [SpecImpProgram]
  , rhleEProgs :: [SpecImpProgram]
  , rhlePost   :: Assertion
  } deriving (Show)
