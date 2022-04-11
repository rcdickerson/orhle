{-# LANGUAGE FlexibleContexts #-}

module Orhle.InvGen.State
  ( AbstractGoodState(..)
  , AbstractGoodStateId
  , AbstractGoodStateIdSet
  , ConcreteGoodState(..)
  , ConcreteGoodStateId
  , ConcreteGoodStateIdSet
  , BadState(..)
  , BadStateId
  , BadStateIdSet
  , States(..)
  , mkClosedStates
  , mkStates
  , stAddBadState
  , stCloseNames
  , stLookupAbstractGoodStates
  ) where

import Ceili.Embedding
import Ceili.Name
import Ceili.ProgState
import Data.IntSet ( IntSet )
import qualified Data.IntSet as IntSet
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set
import Prettyprinter


--------------------------
-- Concrete Good States --
--------------------------

type ConcreteGoodStateId = Int
type ConcreteGoodStateIdSet = IntSet

data ConcreteGoodState t = ConcreteGoodState
  { cgsId    :: ConcreteGoodStateId
  , cgsState :: ProgState t
  } deriving (Eq, Ord)

instance CollectableNames (ConcreteGoodState t) where
  namesIn = namesIn . cgsState

instance Pretty t => Pretty (ConcreteGoodState t) where
  pretty = pretty . cgsState


--------------------------
-- Abstract Good States --
--------------------------

type AbstractGoodStateId = Int
type AbstractGoodStateIdSet = IntSet

data AbstractGoodState t = AbstractGoodState
  { agsId    :: AbstractGoodStateId
  , agsState :: ProgState t
  } deriving (Eq, Ord)

instance CollectableNames (AbstractGoodState t) where
  namesIn = namesIn . agsState

instance Pretty t => Pretty (AbstractGoodState t) where
  pretty = pretty . agsState


----------------
-- Bad States --
----------------

type BadStateId = Int
type BadStateIdSet = IntSet

data BadState t = BadState
  { bsId    :: BadStateId
  , bsState :: ProgState t
  } deriving (Eq, Ord)

instance CollectableNames (BadState t) where
  namesIn = namesIn . bsState

instance Pretty t => Pretty (BadState t) where
  pretty = pretty . bsState


-----------------------
-- State Collections --
-----------------------

data States t = States
  { stNextBsId             :: Int
  , stBadStateIds          :: BadStateIdSet
  , stBadStates            :: Map BadStateId (BadState t)
  , stConcreteGoodStateIds :: ConcreteGoodStateIdSet
  , stConcreteGoodStates   :: Map ConcreteGoodStateId (ConcreteGoodState t)
  , stAbstractGoodStateIds :: AbstractGoodStateIdSet
  , stAbstractGoodStates   :: Map AbstractGoodStateId (AbstractGoodState t)
  , stAllNames             :: Set Name
  }

mkClosedStates :: ( Embeddable Integer t
                  , Ord t )
               => [ProgState t] -> [ProgState t] -> [ProgState t] -> States t
mkClosedStates badStates concreteGoodStates abstractGoodStates =
  let
    nameList             = Set.unions . (map namesIn)
    names                = Set.toList $ Set.unions [ nameList badStates
                                                   , nameList concreteGoodStates
                                                   , nameList abstractGoodStates
                                                   ]
    closedBads      = map (closeNames names) badStates
    closedConGoods  = map (closeNames names) concreteGoodStates
    closedAbsGoods  = map (closeNames names) abstractGoodStates
    badStateSet     = Set.fromList . map (uncurry BadState)          $ zip [0..] closedBads
    goodConStateSet = Set.fromList . map (uncurry ConcreteGoodState) $ zip [0..] closedConGoods
    goodAbsStateSet = Set.fromList . map (uncurry AbstractGoodState) $ zip [0..] closedAbsGoods
  in mkStates badStateSet goodConStateSet goodAbsStateSet

mkStates :: Set (BadState t)
         -> Set (ConcreteGoodState t)
         -> Set (AbstractGoodState t)
         -> States t
mkStates bads conGoods absGoods =
  let
    badIds      = map bsId  $ Set.toList bads
    conGoodIds  = map cgsId $ Set.toList conGoods
    absGoodIds  = map agsId $ Set.toList absGoods
    maxBadId = foldr (\x y -> if x >= y then x else y) (-1) badIds
    nextBsId = maxBadId + 1
  in States { stNextBsId             = nextBsId
            , stBadStateIds          = IntSet.fromList badIds
            , stBadStates            = Map.fromList $ map (\st -> (bsId  st, st)) $ Set.toList bads
            , stConcreteGoodStateIds = IntSet.fromList conGoodIds
            , stConcreteGoodStates   = Map.fromList $ map (\st -> (cgsId st, st)) $ Set.toList conGoods
            , stAbstractGoodStateIds = IntSet.fromList absGoodIds
            , stAbstractGoodStates   = Map.fromList $ map (\st -> (agsId st, st)) $ Set.toList absGoods
            , stAllNames             = Set.unions [ namesIn $ Set.toList bads
                                                  , namesIn $ Set.toList conGoods
                                                  , namesIn $ Set.toList absGoods ]
            }

stAddBadState :: Ord t => ProgState t -> States t -> (BadState t, States t)
stAddBadState progState states =
  let
    newBsId  = stNextBsId states
    badState = BadState newBsId progState
    badIds'  = IntSet.insert newBsId  (stBadStateIds states)
    bads'    = Map.insert newBsId badState (stBadStates states)
    states'  = states { stNextBsId    = newBsId + 1
                      , stBadStateIds = badIds'
                      , stBadStates   = bads'
                      }
  in (badState, states')

stLookupAbstractGoodState :: States t -> AbstractGoodStateId -> AbstractGoodState t
stLookupAbstractGoodState states stateId =
  case Map.lookup stateId (stAbstractGoodStates states) of
    Nothing -> error $ "Abstract good state ID not found: " ++ show stateId
    Just st -> st

stLookupAbstractGoodStates :: States t -> [AbstractGoodStateId] -> [AbstractGoodState t]
stLookupAbstractGoodStates states = map (stLookupAbstractGoodState states)

stCloseNames :: Embeddable Integer t => States t -> ProgState t -> ProgState t
stCloseNames states progState = closeNames (Set.toList $ stAllNames states) progState

closeNames :: Embeddable Integer t => [Name] -> ProgState t -> ProgState t
closeNames names state =
  let ensureIn name st = if Map.member name st
                         then st
                         else Map.insert name (embed (0 :: Integer)) st
  in foldr ensureIn state names
