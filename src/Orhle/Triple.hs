{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Orhle.Triple
  ( HlTriple(..)
  , HleTriple(..)
  , RhleTriple(..)
  ) where

import Ceili.Assertion
import Ceili.Literal
import Ceili.Name
import qualified Data.Set as Set
import Orhle.SpecImp

data HlTriple t = HlTriple
  { hlPre  :: Assertion t
  , hlProg :: SpecImpProgram t
  , hlPost :: Assertion t
  } deriving (Show)

data HleTriple t = HleTriple
  { hlePre  :: Assertion t
  , hleProg :: SpecImpProgram t
  , hlePost :: Assertion t
  } deriving (Show)

data RhleTriple t = RhleTriple
  { rhlePre    :: Assertion t
  , rhleAProgs :: [SpecImpProgram t]
  , rhleEProgs :: [SpecImpProgram t]
  , rhlePost   :: Assertion t
  } deriving (Show)

instance CollectableNames (RhleTriple t) where
  namesIn (RhleTriple pre aprogs eprogs post) =
    Set.unions [ namesIn pre
               , namesIn aprogs
               , namesIn eprogs
               , namesIn post]

instance Ord t => CollectableLiterals (RhleTriple t) t where
  litsIn (RhleTriple pre aprogs eprogs post) =
    Set.unions [ litsIn pre
               , litsIn aprogs
               , litsIn eprogs
               , litsIn post]
