module Spec
  ( Spec(..)
  , SpecMap
  , SpecMaps(..)
  , addSpec
  , emptySpecMap
  , funList
  , lookupSpec
  , prefixSpecs
  , specAtCallsite
  ) where

import           Assertion        ( Assertion )
import qualified Assertion       as A
import           Data.List        ( isPrefixOf )
import qualified Data.Map        as Map
import           Imp
import qualified MapNames        as Names

data Spec = Spec { params        :: [Var]
                 , choiceVars    :: [A.Ident]
                 , preCondition  :: Assertion
                 , postCondition :: Assertion
                 }

type SpecMap = Map.Map String Spec

data SpecMaps = SpecMaps
  { aspecs :: SpecMap
  , especs :: SpecMap
  }

emptySpecMap :: SpecMap
emptySpecMap = Map.empty

addSpec :: String -> Spec -> SpecMap -> SpecMap
addSpec = Map.insert

lookupSpec :: String -> SpecMap -> Maybe Spec
lookupSpec = Map.lookup

funList :: SpecMap -> [String]
funList = Map.keys

specAtCallsite :: [Var] -> [Var] -> String -> SpecMap -> Maybe ([A.Ident], Assertion, Assertion)
specAtCallsite assignees callParams funName funSpecs = do
  (Spec specParams cvars pre post) <- Map.lookup funName funSpecs
  let rets = retVars $ length assignees
  let bind = Names.substituteAll (rets ++ specParams) (assignees ++ callParams)
  return (cvars, bind pre, bind post)

retVars :: Int -> [Var]
retVars 0   = []
retVars 1   = ["ret!"]
retVars len = map (\i -> "ret!" ++ (show i)) [0..len-1]

prefixSpecs :: String -> SpecMap -> SpecMap
prefixSpecs prefix specs = Map.map prefixSpec $ Map.mapKeys applyPrefix specs
  where
    applyPrefix s = if ("ret!" `isPrefixOf` s) then s else prefix ++ s
    prefixSpec (Spec specParams cvars pre post) = let
      prefixedParams     = map applyPrefix specParams
      prefixedChoiceVars = map (Names.mapNames applyPrefix) cvars
      prefixedPre        = Names.mapNames applyPrefix pre
      prefixedPost       = Names.mapNames applyPrefix post
      in Spec prefixedParams prefixedChoiceVars prefixedPre prefixedPost
