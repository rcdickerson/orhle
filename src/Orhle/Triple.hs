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

instance CollectableNames RhleTriple where
  namesIn (RhleTriple pre aprogs eprogs post) =
    Set.unions [ namesIn pre
               , namesIn aprogs
               , namesIn eprogs
               , namesIn post]

instance CollectableTypedNames RhleTriple where
  typedNamesIn (RhleTriple pre aprogs eprogs post) =
    Set.unions [ typedNamesIn pre
               , typedNamesIn aprogs
               , typedNamesIn eprogs
               , typedNamesIn post]

instance CollectableLiterals RhleTriple where
  litsIn (RhleTriple pre aprogs eprogs post) =
    Set.unions [ litsIn pre
               , litsIn aprogs
               , litsIn eprogs
               , litsIn post]
