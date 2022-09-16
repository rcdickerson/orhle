{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeOperators #-}

module Ceili.Name
  ( CollectableNames(..)
  , FreshableNames(..)
  , Freshener
  , FreshMapping(..)
  , Handle
  , Id
  , MappableNames(..)
  , Name(..)
  , NextFreshIds
  , buildFreshIds
  , buildFreshMap
  , freshenBinop
  , fromString
  , prefix
  , runFreshen
  , substitute
  , substituteAll
  , substituteHandle
  , substituteAllHandles
  ) where

import Ceili.Language.Compose
import Ceili.SMTString ( SMTString(..) )
import Control.Monad.State
import qualified Data.ByteString.Char8 as S8
import Data.List ( intercalate )
import Data.List.Split ( splitOn )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


-----------
-- Names --
-----------

type Handle = String
type Id     = Int
data Name   = Name { nHandle :: Handle
                   , nId     :: Id
                   } deriving (Show, Eq, Ord)

instance CollectableNames Name where
  namesIn = Set.singleton

instance MappableNames Name where
  mapNames = ($)

instance FreshableNames Name where
  freshen = freshReplacement

instance SMTString Name where
  toSMT (Name h 0) = S8.pack h
  toSMT (Name h i) = (S8.pack h) <> "!" <> (S8.pack $ show i)

instance Pretty Name where
  pretty (Name h 0) = pretty h
  pretty (Name h i) = pretty h <> "!" <> pretty i

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


------------------
-- Substitution --
------------------

substitute :: MappableNames a => Name -> Name -> a -> a
substitute from to a = mapNames sub a
  where sub name = if (name == from) then to else name

substituteHandle :: MappableNames a => String -> String -> a -> a
substituteHandle from to a = mapNames (liftHandleMap sub) a
  where sub name = if (name == from) then to else name

substituteAll :: MappableNames a => [Name] -> [Name] -> a -> a
substituteAll from to x = mapNames doSub x
  where
    subMap = Map.fromList $ zip from to
    doSub name = case Map.lookup name subMap of
                   Nothing -> name
                   Just replacement -> replacement

substituteAllHandles :: MappableNames a => [String] -> [String] -> a -> a
substituteAllHandles from to x = mapNames doSub x
  where
    subMap = Map.fromList $ zip from to
    doSub (Name handle nid) = case Map.lookup handle subMap of
                                Nothing -> Name handle nid
                                Just replacement -> Name replacement nid


----------------
-- Freshening --
----------------

type NextFreshIds = Map Handle Id

class FreshableNames a where
  freshen :: a -> Freshener a

instance FreshableNames a => FreshableNames [a] where
  freshen names = mapM freshen names

instance (Ord a, FreshableNames a) => FreshableNames (Set a) where
  freshen names = do
    let elems = Set.toList names
    elems' <- freshen elems
    return $ Set.fromList elems'

instance FreshableNames a => FreshableNames (Maybe a) where
  freshen ma = case ma of
    Nothing -> return Nothing
    Just a  -> return . Just =<< freshen a

instance (FreshableNames (f e), FreshableNames (g e)) => FreshableNames ((f :+: g) e) where
  freshen (Inl f) = return . Inl =<< freshen f
  freshen (Inr g) = return . Inr =<< freshen g

buildFreshIds :: (Foldable a, CollectableNames n) => a n -> NextFreshIds
buildFreshIds names = Map.map (+1) maxMap
  where
    allNames = foldMap namesIn names
    maxMap = foldr newMax Map.empty $ Set.toList allNames
    newMax (Name handle hid) maxes = case Map.lookup handle maxes of
      Nothing     -> Map.insert handle hid maxes
      Just curMax -> Map.insert handle (max curMax hid) maxes

-- Freshening with replacement tracking.
data FreshMapping =
  FreshMapping { fr_nextIds      :: NextFreshIds
               , fr_replacements :: Map Name Name
               }

type Freshener a = State FreshMapping a

setNextId :: Handle -> Id -> Freshener ()
setNextId handle id = do
  FreshMapping nextIds replacements <- get
  put $ FreshMapping (Map.insert handle id nextIds) replacements

advanceId :: Handle -> Freshener Id
advanceId handle = do
  mapping <- get
  let id = case Map.lookup handle (fr_nextIds mapping) of
             Nothing   -> 0
             Just next -> next
  setNextId handle (id + 1)
  return id

setReplacement :: Name -> Name -> Freshener ()
setReplacement from to = do
  FreshMapping nextIds replacements <- get
  put $ FreshMapping nextIds (Map.insert from to replacements)

freshReplacement :: Name -> Freshener Name
freshReplacement name = do
  mapping <- get
  case Map.lookup name (fr_replacements mapping) of
    Just r  -> return r
    Nothing -> do
      let handle = nHandle name
      frId <- advanceId handle
      let replacement = Name handle frId
      setReplacement name replacement
      return replacement

freshenBinop :: FreshableNames a => (a -> a -> b) -> a -> a -> Freshener b
freshenBinop op lhs rhs = do
  lhs' <- freshen lhs
  rhs' <- freshen rhs
  return $ op lhs' rhs'

runFreshen :: FreshableNames a => NextFreshIds -> a -> (NextFreshIds, a)
runFreshen nextIds x =
  let (x', mapping) = runState (freshen x) $ FreshMapping nextIds Map.empty
  in (fr_nextIds mapping, x')

buildFreshMap :: Traversable t => NextFreshIds -> t Name -> (NextFreshIds, Map Name Name)
buildFreshMap nextIds names =
  let
    replacements  = mapM freshReplacement names
    mapping       = FreshMapping nextIds Map.empty
    (_, mapping') = runState replacements mapping
  in (fr_nextIds mapping', fr_replacements mapping')


-------------------
-- Collect Names --
-------------------

class CollectableNames a where
  namesIn :: a -> Set Name

instance CollectableNames a => CollectableNames [a] where
  namesIn as = Set.unions $ map namesIn as

instance (CollectableNames (f e), CollectableNames (g e)) => CollectableNames ((f :+: g) e) where
  namesIn (Inl f) = namesIn f
  namesIn (Inr g) = namesIn g


---------------
-- Map Names --
---------------

class MappableNames a where
  mapNames :: (Name -> Name) -> a -> a

instance MappableNames a => MappableNames (Maybe a) where
  mapNames _ Nothing  = Nothing
  mapNames f (Just a) = Just $ mapNames f a

instance MappableNames a => MappableNames [a] where
  mapNames f as = map (mapNames f) as

instance (MappableNames a, Ord a) => MappableNames (Set a) where
  mapNames f as = Set.map (mapNames f) as

instance (MappableNames (f e), MappableNames (g e)) => MappableNames ((f :+: g) e) where
  mapNames func (Inl f) = Inl $ mapNames func f
  mapNames func (Inr g) = Inr $ mapNames func g
