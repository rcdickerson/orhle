{-# LANGUAGE FlexibleContexts #-}

module Orhle.InvGen.StateConc
  (GoodState(..)
  , GoodStateId
  , GoodStateIdSet
  , BadState(..)
  , BadStateId
  , BadStateIdSet
  , States(..)
  , mkClosedStates
  , mkStates
  , stAddBadState
  , stCloseNames
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


-----------------
-- Good States --
-----------------

type GoodStateId = Int
type GoodStateIdSet = IntSet

data GoodState t = GoodState
  { gsId    :: GoodStateId
  , gsState :: ProgState t
  } deriving (Eq, Ord)

instance CollectableNames (GoodState t) where
  namesIn = namesIn . gsState

instance Pretty t => Pretty (GoodState t) where
  pretty = pretty . gsState


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
  { stNextBsId     :: Int
  , stBadStateIds  :: BadStateIdSet
  , stBadStates    :: Map BadStateId (BadState t)
  , stGoodStateIds :: GoodStateIdSet
  , stGoodStates   :: Map GoodStateId (GoodState t)
  , stAllNames     :: Set Name
  }

mkClosedStates :: ( Embeddable Integer t
                  , Ord t )
               => [ProgState t] -> [ProgState t] -> States t
mkClosedStates badStates goodStates =
  let
    nameList     = Set.unions . (map namesIn)
    names        = Set.toList $ Set.union (nameList badStates) (nameList goodStates)
    closedBads   = map (closeNames names) badStates
    closedGoods  = map (closeNames names) goodStates
    badStateSet  = Set.fromList . map (uncurry BadState)  $ zip [0..] closedBads
    goodStateSet = Set.fromList . map (uncurry GoodState) $ zip [0..] closedGoods
  in mkStates badStateSet goodStateSet

mkStates :: Set (BadState t)
         -> Set (GoodState t)
         -> States t
mkStates bads goods =
  let
    badIds   = map bsId  $ Set.toList bads
    goodIds  = map gsId $ Set.toList goods
    maxBadId = foldr (\x y -> if x >= y then x else y) (-1) badIds
    nextBsId = maxBadId + 1
  in States { stNextBsId     = nextBsId
            , stBadStateIds  = IntSet.fromList badIds
            , stBadStates    = Map.fromList $ map (\st -> (bsId  st, st)) $ Set.toList bads
            , stGoodStateIds = IntSet.fromList goodIds
            , stGoodStates   = Map.fromList $ map (\st -> (gsId st, st)) $ Set.toList goods
            , stAllNames     = Set.unions [ namesIn $ Set.toList bads
                                          , namesIn $ Set.toList goods
                                          ]
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

stCloseNames :: Embeddable Integer t => States t -> ProgState t -> ProgState t
stCloseNames states progState = closeNames (Set.toList $ stAllNames states) progState

closeNames :: Embeddable Integer t => [Name] -> ProgState t -> ProgState t
closeNames names state =
  let ensureIn name st = if Map.member name st
                         then st
                         else Map.insert name (embed (0 :: Integer)) st
  in foldr ensureIn state names
