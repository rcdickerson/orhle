module Orhle.Name
  ( CollectableNames(..)
  , Handle
  , Id
  , MappableNames(..)
  , NextFreshIds
  , Name(..)
  , Type(..)
  , TypedName(..)
  , buildNextFreshIds
  , freshen
  , freshNames
  , fromString
  , nextFreshName
  , prefix
  , substitute
  , substituteAll
  , substituteHandle
  , substituteAllHandles
  ) where

import           Data.List ( intercalate )
import           Data.List.Split ( splitOn )
import           Data.Map  ( Map, (!) )
import qualified Data.Map as Map
import           Data.Set  ( Set )
import qualified Data.Set as Set
import           Orhle.ShowSMT

-----------
-- Names --
-----------

type Handle = String
type Id     = Int
data Name   = Name { nHandle :: Handle
                   , nId     :: Id
                   } deriving (Show, Eq, Ord)

class CollectableNames a where
  namesIn :: a -> Set Name

class MappableNames a where
  mapNames :: (Name -> Name) -> a -> a

instance CollectableNames Name where
  namesIn = Set.singleton

instance MappableNames Name where
  mapNames = ($)

instance ShowSMT Name where
  showSMT (Name h 0) = h
  showSMT (Name h i) = h ++ "!" ++ (show i)

liftHandleMap :: (String -> String) -> Name -> Name
liftHandleMap f (Name h i) = Name (f h) i

fromString :: String -> Name
fromString str = case splitOn "!" str of
  []    -> Name str 0
  parts -> case (reads $ last parts) :: [(Int, String)] of
    [(i, "")] -> Name (intercalate "!" $ init parts) i
    _         -> Name str 0

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


-----------------
-- Typed Names --
-----------------

data Type = Bool
          | Int
          deriving (Show, Eq, Ord)

instance ShowSMT Type where
  showSMT ty = case ty of
    Bool -> "bool"
    Int  -> "int"

data TypedName = TypedName { tnName :: Name
                           , tnType :: Type
                           } deriving (Show, Eq, Ord)

instance CollectableNames TypedName where
  namesIn (TypedName name _) = Set.singleton name

instance MappableNames TypedName where
  mapNames f (TypedName name ty) = TypedName (f name) ty

instance ShowSMT TypedName where
  showSMT (TypedName name ty) = "(" ++ showSMT name ++ " " ++ showSMT ty ++ ")"
