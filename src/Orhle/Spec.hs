module Orhle.Spec
  ( Spec(..)
  , SpecMap
  , AESpecs(..)
  , addSpec
  , emptySpecMap
  , funList
  , lookupSpec
  , prefixSpecs
  , retVars
  ) where

import           Data.List ( isPrefixOf )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Assertion ( Assertion )
import           Orhle.Name  ( CollectableNames(..)
                             , Name(..)
                             , TypedName(..) )
import qualified Orhle.Name as Name


--------------------
-- Specifications --
--------------------
data Spec = Spec { spec_params        :: [Name]
                 , spec_choiceVars    :: [TypedName]
                 , spec_preCondition  :: Assertion
                 , spec_postCondition :: Assertion
                 } deriving Show

instance CollectableNames Spec where
  namesIn (Spec ps cs pre post) = Set.unions allNames
    where
      allNames = [ Set.fromList ps
                 , Set.unions $ map namesIn cs
                 , namesIn pre
                 , namesIn post ]


----------------------------
-- Specification Mappings --
----------------------------

type SpecMap = Map.Map Name.Handle Spec

emptySpecMap :: SpecMap
emptySpecMap = Map.empty

addSpec :: Name.Handle -> Spec -> SpecMap -> SpecMap
addSpec = Map.insert

lookupSpec :: Name.Handle -> SpecMap -> Maybe Spec
lookupSpec = Map.lookup

funList :: SpecMap -> [Name.Handle]
funList = Map.keys

prefixSpecs :: String -> SpecMap -> SpecMap
prefixSpecs prefix specs = Map.map prefixSpec $ Map.mapKeys applyPrefix specs
  where
    applyPrefix s = if ("ret" `isPrefixOf` s) then s else prefix ++ s
    applyNamePrefix (Name h i) = Name (applyPrefix h) i
    prefixSpec (Spec specParams cvars pre post) = let
      pParams     = map applyNamePrefix specParams
      pChoiceVars = map (Name.mapNames applyNamePrefix) cvars
      pPre        = Name.mapNames applyNamePrefix pre
      pPost       = Name.mapNames applyNamePrefix post
      in Spec pParams pChoiceVars pPre pPost

retVars :: Int -> [Name]
retVars 0   = []
retVars 1   = [Name "ret!" 0]
retVars len = map (\i -> Name ("ret!" ++ show i) 0) [0..(len - 1)]

-------------
-- AESpecs --
-------------

data AESpecs = AESpecs
  { aspecs :: SpecMap
  , especs :: SpecMap
  }

instance CollectableNames AESpecs where
  namesIn (AESpecs as es) = Set.union (allNames as) (allNames es)
    where allNames = Map.foldr (Set.union . namesIn) Set.empty
