module Orhle.Spec
  ( Spec(..)
  , SpecMap
  , AESpecs(..)
  , addSpec
  , emptySpecMap
  , funList
  , lookupSpec
  , prefixSpecs
  , specAtCallsite
  ) where

import           Data.List ( isPrefixOf )
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Orhle.Assertion  ( Assertion )
import qualified Orhle.Assertion as A
import           Orhle.Names  ( Name(..), CollectableNames(..) )
import qualified Orhle.Names as Names


--------------------
-- Specifications --
--------------------
data Spec = Spec { spec_params        :: [Name]
                 , spec_choiceVars    :: [A.Ident]
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

type SpecMap = Map.Map Names.Handle Spec

emptySpecMap :: SpecMap
emptySpecMap = Map.empty

addSpec :: Names.Handle -> Spec -> SpecMap -> SpecMap
addSpec = Map.insert

lookupSpec :: Names.Handle -> SpecMap -> Maybe Spec
lookupSpec = Map.lookup

funList :: SpecMap -> [Names.Handle]
funList = Map.keys

specAtCallsite :: Names.Handle -> [Name] -> [Name] -> SpecMap -> Maybe ([A.Ident], Assertion, Assertion)
specAtCallsite funName assignees callParams funSpecs = do
  (Spec specParams cvars pre post) <- Map.lookup funName funSpecs
  let rets = retVars $ length assignees
  let bind = Names.substituteAll (rets ++ specParams) (assignees ++ callParams)
  return (cvars, bind pre, bind post)

retVars :: Int -> [Name]
retVars 0   = []
retVars 1   = [Name "ret!" 0]
retVars len = map (\i -> Name ("ret!" ++ show i) 0) [0..(len - 1)]

prefixSpecs :: String -> SpecMap -> SpecMap
prefixSpecs prefix specs = Map.map prefixSpec $ Map.mapKeys applyPrefix specs
  where
    applyPrefix s = if ("ret" `isPrefixOf` s) then s else prefix ++ s
    applyNamePrefix (Name h i) = Name (applyPrefix h) i
    prefixSpec (Spec specParams cvars pre post) = let
      pParams     = map applyNamePrefix specParams
      pChoiceVars = map (Names.mapNames applyNamePrefix) cvars
      pPre        = Names.mapNames applyNamePrefix pre
      pPost       = Names.mapNames applyNamePrefix post
      in Spec pParams pChoiceVars pPre pPost


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
