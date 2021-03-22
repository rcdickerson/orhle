--
-- Relational reasoning is rife with multiple "copies" of the same variable, and
-- program verification in general requires a lot of variable freshening. We
-- centralize these concerns using the following ontology:
--
-- 1) A "handle" is the string which identifies a variable.
-- 2) An "id" identifies some copy or freshening of a handle.
-- 3) A "name" is a (handle, id) pair.
--
-- ORHLE reperesents most variables as names, i.e. (handle, id) pairs. Freshening
-- operations are cleanly handled as mappings over IDs.
--
module Orhle.Names
  ( CollectableNames(..)
  , Handle
  , Id
  , MappableNames(..)
  , NextFreshIds
  , Name(..)
  , buildNextFreshIds
  , freshen
  , prefix
  , substitute
  , substituteAll
  , substituteHandle
  , substituteAllHandles
  ) where

import           Data.Map  ( Map, (!) )
import qualified Data.Map as Map
import           Data.Set  ( Set )

type Handle = String
type Id     = Int
data Name   = Name { nHandle :: Handle
                   , nId     :: Id
                   } deriving (Eq, Ord)

instance Show Name where
  show (Name h 0) = h
  show (Name h i) = h ++ "!" ++ (show i)

class CollectableNames a where
  namesIn :: a -> Set Name

class MappableNames a where
  mapNames :: (Name -> Name) -> a -> a

liftHandleMap :: (String -> String) -> Name -> Name
liftHandleMap f (Name h i) = Name (f h) i

prefix :: MappableNames a => String -> a -> a
prefix pre a = mapNames (liftHandleMap $ (++) pre) a

substitute :: MappableNames a => Name -> Name -> a -> a
substitute from to a = mapNames sub a
  where sub name = if (name == from) then to else name

substituteHandle :: MappableNames a => String -> String -> a -> a
substituteHandle from to a = mapNames (liftHandleMap sub) a
  where sub name = if (name == from) then to else name

substituteAll :: MappableNames a => [Name] -> [Name] -> a -> a
substituteAll from to x = foldr (uncurry substitute) x $ zip from to

substituteAllHandles :: MappableNames a => [String] -> [String] -> a -> a
substituteAllHandles from to x = foldr (uncurry substituteHandle) x $ zip from to

type NextFreshIds = Map Handle Id

buildNextFreshIds :: Foldable a => a Name -> NextFreshIds
buildNextFreshIds names = Map.map (+1) maxMap
  where
    maxMap = foldr newMax Map.empty names
    newMax (Name handle id) maxes = case Map.lookup handle maxes of
      Nothing     -> Map.insert handle id maxes
      Just curMax -> Map.insert handle (max curMax id) maxes

nextFreshId :: Handle -> NextFreshIds -> (Id, NextFreshIds)
nextFreshId handle nextIds =
  case Map.lookup handle nextIds of
    Nothing   -> (0, Map.insert handle 1 nextIds)
    Just next -> (next, Map.insert handle (next + 1) nextIds)

nextFreshName :: Name -> NextFreshIds -> (Name, NextFreshIds)
nextFreshName (Name handle _) nextIds =
  let (id', nextIds') = nextFreshId handle nextIds
  in  (Name handle id', nextIds')

freshNames :: Foldable f => f Name -> NextFreshIds -> (Map Name Name, NextFreshIds)
freshNames names nextIds = foldr f (Map.empty, nextIds) names
  where f name (replacements, nextIds) =
          case Map.lookup name replacements of
            Just _     -> (replacements, nextIds)
            Nothing    -> let (name', nextIds') = nextFreshName name nextIds
                          in (Map.insert name name' replacements, nextIds')

freshen :: Traversable t => t Name -> NextFreshIds -> (t Name, NextFreshIds)
freshen names nextIds =
  (fmap (replacements!) names, nextIds')
  where (replacements, nextIds') = freshNames names nextIds
