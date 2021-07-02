module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  ) where

import Ceili.Assertion
import Ceili.Language.FunImp

data HlTriple = HlTriple
  { hlPre  :: Assertion
  , hlProg :: FunImpProgram
  , hlPost :: Assertion
  } deriving (Show)

data HleTriple = HleTriple
  { hlePre  :: Assertion
  , hleProg :: FunImpProgram
  , hlePost :: Assertion
  } deriving (Show)

data RhleTriple = RhleTriple
  { rhlePre    :: Assertion
  , rhleAProgs :: [FunImpProgram]
  , rhleEProgs :: [FunImpProgram]
  , rhlePost   :: Assertion
  } deriving (Show)
